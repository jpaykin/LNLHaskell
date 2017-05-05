{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, 
             RankNTypes, LambdaCase
#-}

-- Implementation of density matrix interpretation of quantum computation
module LinTrans2 where

import Prelim

import qualified Data.Complex as C 
import Data.Complex (Complex(..))
import Control.Monad.State.Lazy
import Data.Singletons
import Data.Maybe (fromJust)
--import Data.Tuple hiding (swap)
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


--------------
-- Matrices --
--------------

-- A matrix Matrix (m,n) f of dimension 2^m × 2^n is a function f from pairs of
-- nats to ℂ
data Matrix = Matrix { dim :: (Int,Int)
                     , idx :: (Int, Int) -> ℂ
                     }
dom :: Matrix -> [Int]
dom (Matrix (m,_) _) = [0..(2^m)-1]

cod :: Matrix -> [Int]
cod (Matrix (_,n) _) = [0..(2^n)-1]

mkMatrix :: (Int,Int) -> [[ℂ]] -> Matrix
mkMatrix (m,n) ls = Matrix (m,n) $ \(i,j) -> (ls !! i) !! j

--------------
-- Printing --
--------------

rows :: Matrix -> [[ℂ]]
rows mat = f <$> dom mat
  where
    f i = (\j -> idx mat (i,j)) <$> cod mat
showRows :: Matrix -> [String]
showRows mat = show <$> rows mat
instance Show Matrix where
  show mat = unlines $ showRows mat


---------------------------------------
-- Primitive matrices and operations --
---------------------------------------

ident :: Int -> Matrix
ident n = Matrix (n,n) $ \(i,j) -> if i == j then 1 else 0

transpose :: Matrix -> Matrix
transpose (Matrix (m,n) f) = Matrix (n,m) $ \(i,j) -> f (j,i)

dot :: Matrix -> Matrix -> ℂ
dot v1 v2 | snd (dim v1) == fst (dim v2) =
            foldl (+) 0 $ (\x -> idx v1 (0,x) * idx v2 (x,0)) <$> dom v2
          | otherwise = error "Mismatched dimensions when taking dot product"

row :: Int -> Matrix -> Matrix
row i (Matrix (_,n) f) = Matrix (0,n) $ \(_,j) -> f(i,j)

col :: Int -> Matrix -> Matrix
col j (Matrix (m,_) f) = Matrix (m,0) $ \(i,_) -> f(i,j)

plusM :: Matrix -> Matrix -> Matrix
plusM (Matrix dim1 f1) (Matrix dim2 f2) | dim1 == dim2 = 
       Matrix dim1 $ \(i,j) -> f1(i,j) + f2(i,j)
plusM _ _ | otherwise    = error "Mismatched dimensions when adding matrices"

multM :: Matrix -> Matrix -> Matrix
multM mat1 mat2 | n1 == m2 = 
    Matrix (m1,n2) $ \(i,j) -> dot (row i mat1) (col j mat2)
  where
    (m1,n1) = dim mat1
    (m2,n2) = dim mat2
multM _ _ | otherwise = error "Mismatched dimensions when multiplying matrices"

kron :: Matrix -> Matrix -> Matrix
kron (Matrix (m1,n1) f1) (Matrix (m2,n2) f2) =
    Matrix (m1*n1, m2*n2) $ \(i,j) -> 
           f1 (i `div` 2^m2, j `div` 2^n2) * f2 (i `mod` 2^m2, j `mod` 2^n2)

zero n = Matrix (n,n) $ \_ -> 0

scale :: ℂ -> Matrix -> Matrix
scale c (Matrix (m,n) f) = Matrix (m,n) $ \(i,j) -> c * f(i,j)

{-
trace :: forall m. SingI m => Matrix m m -> ℂ
trace mat = foldr f 0 ls
  where
    ls = allBNat (sing :: Sing m)
    f i x = mat (i,i) + x
-}

----------------------
-- Quantum Matrices --
----------------------

ket0 = mkMatrix (1,0) [[1],[0]]
ket1 = mkMatrix (1,0) [[0],[1]]
density0 = ket0 * transpose ket0
density1 = ket1 * transpose ket1
newD True  = density1
newD False = density0

hadamard = mkMatrix (1,1) [[1/sqrt 2, 1/sqrt 2]
                          ,[1/sqrt 2, -1/sqrt 2]]

pauliX = mkMatrix (1,1) [[0,1]
                       ,[1,0]]
pauliY = mkMatrix (1,1) [[0,-1]
                       ,[i,0]]
pauliZ = mkMatrix (1,1) [[1,0]
                       ,[0,-1]]

cnot = mkMatrix (2,2) [[1,0,0,0]
                      ,[0,1,0,0]
                      ,[0,0,0,1]
                      ,[0,0,1,0]]





------------------
-- Permutations --
------------------

-- encode and decode modulo a key k
encode :: Int -> [Int] -> Int
encode k [] = 0
encode k (i : ls) = i + k * encode k ls

decode :: Int -> Int -> [Int]
decode k i | i == 0 = []
decode k i | otherwise = i `mod` k : decode k (i `div` k)

fromAssocList :: [(Int,Int)] -> Int -> Int
fromAssocList []           = id
fromAssocList ((a,b) : ls) = assocFun a b . fromAssocList ls
  where
    assocFun a b i = if i == a then b else i

-- Check if two lists are equal up to the permutation specified, i.e.
-- if permuting ls1 by f is equal to ls2
isPermutation :: Eq a => (Int -> Int) -> [a] -> [a] -> Bool
isPermutation f ls1 ls2 = all (\i -> ls1 !! i == ls2 !! f i) [0..len]
  where
    len = length ls1
    

swapFun :: Int -> (Int -> Int) -> Matrix
swapFun k f = Matrix (k,k) $ \(i,j) -> 
    if isPermutation f (decode k i) (decode k j) then 1 else 0

-- swap takes a list of qubit/bit variables and produces a matrix that permutes
-- those qubits.
-- i.e. swap ls |φ_0 ⋯ φ_n⟩ = |φ_f(0) ⋯ ρ_f(n)⟩ 
-- where f = fromAssocList ls
swap :: Int -> [Int] -> Matrix
swap k ls = swapFun k $ fromAssocList $ zip [0..] ls



-------------------
-- Density Monad --
-------------------

-- A density monad is a nondeterminism state monad:
-- Density -> [Density]
-- An element op of type DensityMonad corresponds to the superoperator
-- \ρ -> ∑ (op ρ)
type DensityMonad = StateT Matrix []

newM :: Bool -> DensityMonad Int
newM b = do
    ρ ← get
    put $ ρ `kron` newD b
    return $ fst (dim ρ)

-- runQ applies the superoperator to the identity density matrix of size 1.
runQ :: DensityMonad a -> [(a,Matrix)]
runQ m = runStateT m (ident 0)

-- getDensity combines the result of runQ into a single density matrix
getDensity :: DensityMonad a -> Matrix
getDensity m = foldr f (zero n) ls
  where
    ls = runQ m
    n = fst . dim . snd $ head ls
    f (_,ρ) ρ0 = ρ + ρ0



-----------------
-- Application --
-----------------


super :: Matrix -> DensityMonad ()
super mat = do ρ ← get
               put $ mat * ρ * transpose mat

applyMatrix :: Matrix -> [Int] -> DensityMonad ()
applyMatrix mat ls = do super $ swap n ls  -- moves the relevant qubits to the front
                        super mat -- applies operation
                        super . transpose $ swap n ls -- moves the qubits back to where they were
  where
    (n,_) = dim mat

branch :: DensityMonad a -> DensityMonad a -> DensityMonad a
branch m0 m1 = StateT $ \ρ -> [runStateT m0 ρ, runStateT m1 ρ] >>= id

measM :: Int -> DensityMonad Bool
measM i = branch (applyMatrix density0 [i] >> return False) (applyMatrix density1 [i] >> return True)


------------------
-- Num instance --
------------------

instance Num Matrix where
  (+) = plusM
  mat1 - mat2 = mat1 `plusM` scale (-1) mat2
  (*) = multM
  abs = undefined
  signum mat = undefined -- trace?
  fromInteger n = ident $ fromInteger n

-------------------
-- Show Instance --
-------------------

instance Show (DensityMonad a) where
  show = show . getDensity

{-


------------------
-- Num instance --
------------------

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




-- Debugging help
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



-}
