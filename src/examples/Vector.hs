{-# LANGUAGE
    KindSignatures, DataKinds, GADTs, InstanceSigs, FlexibleInstances,
    TypeApplications, ScopedTypeVariables, TypeOperators
#-}

module Vector where

import Prelim
import Data.Array
import Linear hiding (vector) -- linear algebra library 

type Vector n = Array (BNat n)

vector :: KnownNat n => SNat n -> [a] -> Vector n a
vector n ls = listArray (fromIntegerBNat n 0,maxBNat n) ls

instance KnownNat n => Applicative (Vector n) where
  pure a = vector n $ replicate (toInt n) a
    where
      n = sNat @n
  
  (<*>) :: Vector n (a -> b) -> Vector n a -> Vector n b
  v1 <*> v2 = vector (sNat @n) $ elems v1 <*> elems v2 

instance KnownNat n => Additive (Vector n) where
  zero :: Num a => Vector n a
  zero = vector n $ replicate (toInt n) 0 where
    n = sNat @n

type Matrix m n a = Vector m (Vector n a)

(⊗) :: forall m1 n1 m2 n2 a. 
       (KnownNat m1, KnownNat n1, KnownNat m2, KnownNat n2, Num a)
    => Matrix m1 n1 a -> Matrix m2 n2 a -> Matrix (m1 `Times` m2) (n1 `Times` n2) a
mat1 ⊗ mat2 = flatten1 . vector (sNat @m1) $ f1 <$> ls1
  where
    ls1 :: [[a]]
    ls1 = elems <$> elems mat1

    f1 :: [a] -> Matrix m2 (n1 `Times` n2) a
    f1 as = flatten2 . vector (sNat @n1) $ f2 <$> as

    f2 :: a -> Matrix m2 n2 a
    f2 a = a *!! mat2

    -- TODO: work over [[a]]
    flatten1 :: Vector r (Matrix m n a) -> Matrix (r `Times` m) n a
    flatten1 v = undefined
    
    flatten2 :: Vector r (Matrix m n a) -> Matrix m (r `Times` n) a
    flatten2 = undefined

swapRow :: (BNat m,BNat m) -> Matrix m n a -> Matrix m n a
swapRow = undefined

swapRows :: [(BNat m,BNat m)] -> Matrix m n a -> Matrix m n a
swapRows = undefined

swapCol :: (BNat m,BNat m) -> Matrix m n a -> Matrix m n a
swapCol = undefined

swapCols :: (BNat m,BNat m) -> Matrix m n a -> Matrix m n a
swapCols = undefined

