{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, 
             RankNTypes
#-}

-- Implementation of density matrix interpretation of quantum computation
module LinTrans where

import Prelim

import qualified Data.Complex as C 
import Data.Complex (Complex(..))
import Control.Monad.State.Lazy
import Data.Singletons

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
transposeD (Density ρ) = Density $ transpose ρ

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

mult :: SingI n => Matrix m n -> Matrix n p -> Matrix m p
mult mat1 mat2 (i,j) = dot sing (row i mat1) (col j mat2)

kron :: forall m1 m2 n1 n2. (SingI m1, SingI n1, SingI m2, SingI n2)
     => Matrix m1 n1 -> Matrix m2 n2 -> Matrix (m1 `Times` m2) (n1 `Times` n2)
kron mat1 mat2 (BNat i,BNat j) = mat1 (bNat i1, bNat j1) * mat2 (bNat i2,bNat j2)
  where
    i1 = i `divSNat` (sing :: Sing m2)
    i2 = i `modSNat` (sing :: Sing n2)
    j1 = j `divSNat` (sing :: Sing m2)
    j2 = j `divSNat` (sing :: Sing n2)

trace :: forall m. SingI m => Matrix m m -> ℂ
trace mat = foldr f 0 ls
  where
    ls = allBNat (sing :: Sing m)
    f i x = mat (i,i) + x

--------------------------------------------------------------------

-- BUG HERE, I THINK
-- expand applies the matrix when the map is defined, is the identity elsewhere
expand :: Matrix m m -> (BNat p -> Maybe (BNat m)) -> Matrix p p
expand mat f (i,j) = case (f i, f j) of
    (Just i',Just j') -> mat (i',j')
    (_,_)             -> ident (i,j)

applyMatrix :: SingI p 
            => Matrix m m -> (BNat p -> Maybe (BNat m)) -> Matrix p p -> Matrix p p
applyMatrix mat f ρ = expand (transpose mat) f `mult` ρ `mult` expand mat f


listToMap :: forall p m. (SingI p, SingI m) => [Int] -> BNat p -> Maybe (BNat m)
listToMap ls n = fromIntegral <$> (listToMap' ls $ fromIntegral n)
  where
    listToMap' :: [Int] -> Int -> Maybe Int
    listToMap' ls i | i < length ls = Just $ ls !! i
    listToMap' ls i | otherwise     = Nothing


--------------------------------------------------------------

data Density where
  Density :: SingI n => Matrix n n -> Density
instance Show Density where
  show (Density m) = show m

size :: forall m. SingI m => Matrix m m -> Int
size _ = toInt (sing :: Sing m)
sizeD :: Density -> Int
sizeD (Density mat) = size mat


kronD :: Density -> Density -> Density
kronD (Density mat1) (Density mat2) = kronD' mat1 mat2
  where
    kronD' :: forall m n. (SingI m, SingI n) => Matrix m m -> Matrix n n 
           -> Density -- Matrix (m `Times` n) (m `Times n`)
    kronD' mat1 mat2 = withSingI (timesSNat (sing :: Sing m) (sing :: Sing n)) $
                       Density $ mat1 `kron` mat2

-- Some matrices
type Two = S (S Z)
type Three = S Two
type Four = S Three

square :: forall n. SingI n => [ℂ] -> Matrix n n
square ls = matrix ls

density0 :: Matrix Two Two
density0 = matrix [1,0
                  ,0,0]

density1 :: Matrix Two Two
density1 = matrix [0,0
                  ,0,1]

hadamard = square @Two $ [1/sqrt 2, 1/sqrt 2
                         ,1/sqrt 2, -1/sqrt 2]

 

pauliX = square @Two $ [0,1,1,0]
pauliY = square @Two $ [0,-i,i,0]
pauliZ = square @Two $ [1,0,0,-1]

cnotD  = square @Four $ [1,0,0,0
                        ,0,1,0,0
                        ,0,0,0,1
                        ,0,0,1,0]

newD :: Bool -> Matrix Two Two
newD True = density1
newD False = density0 

densityI :: Sing m -> Matrix m m -> Density
densityI m mat = withSingI m $ Density mat

identD :: Int -> Density
identD n = case fromIntegral @_ @(SomeSing Nat) n of 
             SomeSing n' -> densityI n' ident

type DensityMonad = StateT Density []

applyMatrixD :: SingI m => Matrix m m -> [Int] -> Density -> Density
applyMatrixD mat perm (Density ρ) = 
    Density $ applyMatrix mat (listToMap perm) ρ



newM :: Bool -> DensityMonad Int
newM b = do
    ρ <- get
    put $ ρ `kronD` (Density $ newD b)
    return $ sizeD ρ

applyUnitaryM :: SingI m => Matrix m m -> [Int] -> DensityMonad ()
applyUnitaryM mat ls = get >>= \ρ -> put $ applyMatrixD mat ls ρ

measM :: Int -> DensityMonad Bool
measM i = do
    ρ <- get
    (b,ρ') <- lift [ (False, applyMatrixD density0 [i] ρ)
                   , (True,  applyMatrixD density1 [i] ρ) ]
    put ρ'
    return b

runQ :: DensityMonad a -> [(a,Density)]
runQ m = runStateT m (Density @(S Z) ident)

-- todo: getDensity :: DensityMoand a -> Density

-- Num instance
instance (SingI m, SingI n) => Num (Matrix m n) where
  (+) mat1 mat2 (i,j) = mat1(i,j) + mat2(i,j)
  (-) mat1 mat2 (i,j) = mat1(i,j) - mat2(i,j)
  (*) mat1 mat2 (i,j) = mat1(i,j) * mat2(i,j)
  abs mat (i,j) = abs $ mat(i,j)
  signum mat = undefined -- trace mat
  fromInteger n = matrix . repeat $ fromIntegral n
--instance Num Density where
--  Density mat1 + Density mat2 = Density $ mat1 + mat2
