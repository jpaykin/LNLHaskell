{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, 
             RankNTypes, LambdaCase
#-}

-- Implementation of density matrix interpretation of quantum computation
module LinTrans where

import Prelim

import qualified Data.Complex as C 
import Data.Complex (Complex(..))
import Control.Monad.State.Lazy
import Data.Singletons
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Unsafe.Coerce
import Data.Constraint (Dict(..))
import Data.List ( (\\) )
import qualified Debug.Trace as Tr


-- I don't like the show instance for ℂ
newtype ℂ = ℂ (Complex Double)

liftC :: (Complex Double -> Complex Double) -> ℂ -> ℂ
liftC f (ℂ c) = ℂ $ f c

i :: ℂ
i = ℂ $ 0 :+ 1
conjugate = liftC C.conjugate
instance Num ℂ where
  ℂ m + ℂ n = ℂ $ m + n
  ℂ m - ℂ n = ℂ $ m - n
  ℂ m * ℂ n = ℂ $ m * n
  abs = liftC abs
  signum = liftC signum
  fromInteger = ℂ . fromInteger 
instance Fractional ℂ where
  fromRational = ℂ . fromRational
  ℂ m / ℂ n    = ℂ $ m / n
instance Floating ℂ where
  pi    = ℂ $ pi
  exp   = liftC exp
  log   = liftC log
  sin   = liftC sin
  cos   = liftC cos
  asin  = liftC asin
  acos  = liftC acos
  atan  = liftC atan
  sinh  = liftC sinh
  cosh  = liftC cosh
  asinh = liftC asinh
  acosh = liftC acosh
  atanh = liftC atanh
instance Show ℂ where
  show (ℂ (α :+ β)) =   if β == 0 then show α 
                        else if α == 0 then show β ++ "i"
                        else show α ++ " + " ++ show β ++ "i"



type Matrix m n = (BNat m,BNat n) -> ℂ
type Squared n = Matrix (Two `RaiseTo` n) (Two `RaiseTo` n)

matrix :: forall m n. (SingI m, SingI n) => [ℂ] -> Matrix m n
matrix ls (i,j) = ls !! (n * fromIntegral i + fromIntegral j)
  where
    n = toInt (sing :: Sing n)

rows :: forall m n. (SingI m, SingI n) => Matrix m n -> [[ℂ]]
rows mat = fmap f $ allBNat (sing :: Sing m)
  where
    f i = fmap (\j -> mat (i,j)) $ allBNat (sing :: Sing n)

showRows :: (SingI m, SingI n) => Matrix m n -> [String]
showRows mat = show <$> rows mat

instance (SingI m, SingI n) => Show (Matrix m n) where
  show mat = unlines $ showRows mat

ident :: Matrix m m
ident (i,j) = if i==j then 1 else 0

transpose :: Matrix m n -> Matrix n m
transpose mat (i,j) = conjugate $ mat (j,i)

transposeD :: Density -> Density 
transposeD (Density m ρ) = Density m $ transpose ρ

pruneRows :: Sing m -> Matrix (S m) n -> Matrix m n
pruneRows m mat (i,j) = mat (raise m i,j)

pruneCols :: Sing n -> Matrix m (S n) -> Matrix m n
pruneCols n mat (i,j) = mat (i,raise n j)

dot :: Sing n -> Matrix (S Z) n -> Matrix n (S Z) -> ℂ
dot SZ _ _ = 0
dot (SS n) mat1 mat2 = 
    (mat1 (0,maxBNat (SS n)) * mat2 (maxBNat (SS n), 0)) 
  + dot n (pruneCols n mat1) (pruneRows n mat2)

row :: BNat m -> Matrix m n -> Matrix (S Z) n
row i mat (_,j) = mat (i,j)

col :: BNat n -> Matrix m n -> Matrix m (S Z)
col j mat (i,_) = mat (i,j)

mult :: forall m n p. SingI n => Matrix m n -> Matrix n p -> Matrix m p
mult mat1 mat2 (i,j) = 
--  Tr.trace ("Composing for intermediate " ++ show (sing :: Sing n)) $
    dot sing (row i mat1) (col j mat2)

kron :: forall m1 m2 n1 n2. (SingI m1, SingI n1, SingI m2, SingI n2)
     => Matrix m1 n1 -> Matrix m2 n2 -> Matrix (m1 `Times` m2) (n1 `Times` n2)
kron mat1 mat2 (BNat i,BNat j) = 
--    Tr.trace ("Computing ⊗ for " ++ show (m1, n1) ++ "×" ++ show (m2, n2)) $
    mat1 (bNat i1, bNat j1) * mat2 (bNat i2,bNat j2)
  where
    i1 = i `divSNat` (sing :: Sing m2)
    i2 = i `modSNat` (sing :: Sing m2)
    j1 = j `divSNat` (sing :: Sing n2)
    j2 = j `modSNat` (sing :: Sing n2)
    m1 = (sing :: Sing m1)
    m2 = (sing :: Sing m2)
    n1 = (sing :: Sing n1)
    n2 = (sing :: Sing n2)

trace :: forall m. SingI m => Matrix m m -> ℂ
trace mat = foldr f 0 ls
  where
    ls = allBNat (sing :: Sing m)
    f i x = mat (i,i) + x

--------------------------------------------------------------------

-- produces an association list
listToAssoc :: forall n. SingI n => [Int] -> [(BNat n, BNat n)]
listToAssoc ls = (fromIntegral <$> [0..n]) `zip` (fromIntegral <$> pad ls)
  where
    n = maxBNat (sing :: Sing n)

pad :: [Int] -> [Int]
pad ls = ls ++ ([0..] \\ ls)

mkPermutation :: [(BNat n,BNat n)] -> BNat n -> BNat n
mkPermutation ls i = 
  case lookup i ls of
    Just i' -> i'
    Nothing -> error $ "Permutation " ++ show ls 
                        ++ " not well defined at index " ++ show i

permute :: forall m. SingI m => [(BNat m, BNat m)] -> Matrix m m -> Matrix m m
permute ls mat (i,j) = mat (mkPermutation ls i, mkPermutation ls j)

expand :: forall m n. (SingI m, SingI n) 
       => [(BNat (m `Times` n), BNat (m `Times` n))] 
       -> Matrix m m -> Matrix (m `Times` n) (m `Times` n)
expand ls mat = Tr.trace ("Expanding..." ++ show mat) $
                withSingI (timesSNat (sing :: Sing m) (sing :: Sing n)) $ 
                  permute ls $ mat `kron` ident @n

applyMatrix :: forall m p. (SingI m, SingI p, (p < m) ~ 'False)
            => Squared m -> [Int] -> Squared p -> Squared p
applyMatrix mat ls ρ = 
  Tr.trace ("Applying " ++ show ls) $
  case raiseToPlus two m minus of {Dict ->
  case plusMinus m p of {Dict -> 
  withSingI (raiseToSNat two m) $
  withSingI (raiseToSNat two minus) $ 
  withSingI (raiseToSNat two p) $
    let mat1 = expand @(Two `RaiseTo` m) @(Two `RaiseTo` (p `Minus` m)) 
                       (swap <$> ls') (transpose mat)
        mat2 = expand @(Two `RaiseTo` m) @(Two `RaiseTo` (p `Minus` m)) ls' mat
        res  = Tr.trace "Middle of application" $
               mat1 `mult` ρ `mult` mat2
    in mat1 `seq` mat2 `seq` res `seq` Tr.trace "End of application" res
  }}
  where
    ls' :: [(BNat (Two `RaiseTo` p), BNat (Two `RaiseTo` p))]
    ls' = withSingI (raiseToSNat two p) $ listToAssoc ls
    m = (sing :: Sing m)
    p = (sing :: Sing p)
    minus :: Sing (p `Minus` m)
    minus = minusSNat p m

--------------------------------------------------------------

data Density where
  Density :: Sing n -> Squared n -> Density
instance Show Density where
  show (Density n m) = withSingI (two `raiseToSNat` n) $ show m

size :: forall m. SingI m => Matrix m m -> Int
size _ = toInt (sing :: Sing m)
logsizeD :: Density -> Int
logsizeD (Density n mat) = toInt n
sizeD :: Density -> Int
sizeD ρ = 2 ^ logsizeD ρ



kronD :: Density -> Density -> Density
kronD (Density m mat1) (Density n mat2) = 
    kronD' m n mat1 mat2
  where
    kronD' :: forall m n. Sing m -> Sing n -> Squared m -> Squared n 
           -> Density
    kronD' m n mat1 mat2 = 
--      Tr.trace ("Computing ⊗ for " ++ show m ++ "×" ++ show n) $
      withSingI (raiseToSNat two n) $ 
      withSingI (raiseToSNat two m) $ 
      withSingI (raiseToSNat two (plusSNat m n)) $
      case raiseToPlus two m n of 
        Dict -> Density (m `plusSNat` n) $ mat1 `kron` mat2

-- Some matrices

square :: forall n. SingI n => [ℂ] -> Squared n
square ls = withSingI (two `raiseToSNat` (sing :: Sing n)) $ matrix ls

density0 :: Matrix Two Two
density0 = matrix [1,0
                  ,0,0]

density1 :: Matrix Two Two
density1 = matrix [0,0
                  ,0,1]

hadamard = square @One $ [1/sqrt 2, 1/sqrt 2
                         ,1/sqrt 2, -1/sqrt 2]

 

pauliX = square @One $ [0,1,1,0]
pauliY = square @One $ [0,-i,i,0]
pauliZ = square @One $ [1,0,0,-1]

cnotD  = square @Two $ [1,0,0,0
                       ,0,1,0,0
                       ,0,0,0,1
                       ,0,0,1,0]

newD :: Bool -> Squared One
newD True  = density1
newD False = density0 

--densityI :: Sing m -> Matrix m m -> Density
--densityI m mat = withSingI m $ Density m mat

identD :: Int -> Density
identD n = case fromIntegral @_ @(SomeSing Nat) n of 
             SomeSing n' -> Density n' ident

type DensityMonad = StateT Density []

applyMatrixD :: forall m. SingI m => Squared m -> [Int] -> Density -> Density
applyMatrixD mat perm (Density (p :: Sing p) ρ) = 
  Tr.trace ("Applying " ++ mat' ++ " to qubits " ++ show perm ++ " of \n" ++ show (Density p ρ)) $
  case compareSNat p (sing :: Sing m) of
    -- p < m
    Left Dict -> error "Cannot apply matrix to state: matrix too large"
    -- m <= p
    Right Dict -> 
      let res = withSingI p $ Density p $ applyMatrix @m @p mat perm ρ 
      in  res `seq` Tr.trace "Done!" res
  where
    mat' = withSingI (two `raiseToSNat` (sing :: Sing m)) $ show mat


newM :: Bool -> DensityMonad Int
newM b = do
    ρ <- get
    put $ ρ `kronD` (Density one $ newD b)
    return $ sizeD ρ

applyUnitaryM :: forall m. SingI m => Squared m -> [Int] -> DensityMonad ()
applyUnitaryM mat ls = get >>= \ρ -> put $ applyMatrixD @m mat ls ρ

measM :: Int -> DensityMonad Bool
measM i = do
    ρ <- get
    (b,ρ') <- lift [ (False, applyMatrixD @One density0 [i] ρ)
                   , (True,  applyMatrixD @One density1 [i] ρ) ]
    put ρ'
    return b

runQ :: DensityMonad a -> [(a,Density)]
runQ m = runStateT m (Density SZ ident)

-- todo: getDensity :: DensityMoand a -> Density

-- Num instance
instance (SingI m, SingI n) => Num (Matrix m n) where
  (+) mat1 mat2 (i,j) = mat1(i,j) + mat2(i,j)
  (-) mat1 mat2 (i,j) = mat1(i,j) - mat2(i,j)
  (*) mat1 mat2 (i,j) = mat1(i,j) * mat2(i,j)
  abs mat (i,j) = abs $ mat(i,j)
  signum mat = undefined -- trace mat
  fromInteger n = matrix . repeat $ fromIntegral n
instance Num Density where
  Density n1 mat1 + Density n2 mat2 = 
    withSingI (two `raiseToSNat` n1) $
    withSingI (two `raiseToSNat` n2) $
    case eqSNat n1 n2 of 
      Left Dict -> Density n1 $ mat1 + mat2
      Right _   -> error $ "Cannot add mismatched matrices " 
                            ++ show mat1 ++ " and " ++ show mat2
  _ - _ = undefined
  _ * _ = undefined
  abs _ = undefined
  signum = undefined
  fromInteger n = undefined

nil :: Int -> Density
nil n = case fromIntegral n of
          SomeSing n' -> withSingI (two `raiseToSNat` n') $
                         Density n' . matrix $ fromIntegral <$> repeat 0

getDensity :: DensityMonad a -> Density
getDensity m = foldr f (nil n) ls
  where
    ls = runQ m
    n = logsizeD . snd $ head ls
--    nil = case fromIntegral n of 
--            SomeSing n' -> withSingI (two `raiseToSNat` n') $
--                           Density n' . matrix $ fromIntegral <$> [0..]
    f (_,ρ) ρ0 = ρ + ρ0

instance Show (DensityMonad a) where
  show = show . getDensity

m0 = square @Two [1,0,0,0
                 ,0,1,0,0
                 ,0,0,0,1
                 ,0,0,1,0]
rho = Density three $ \case
  (0,0) -> -0.5
  (0,2) ->  0.5
  (3,0) -> -0.5
  (3,2) ->  0.5
  (_,_) -> 0
