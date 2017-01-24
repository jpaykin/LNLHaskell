{-# LANGUAGE
    KindSignatures, DataKinds, GADTs, InstanceSigs, FlexibleInstances,
    TypeApplications, ScopedTypeVariables, TypeOperators
#-}

module Vector where

import Prelim
import Data.Array
import Linear hiding (vector) -- linear algebra library 

-- Bounded natural numbers

data Lt (m :: Nat) (n :: Nat) where
  LtZ :: Lt 'Z ('S n)
  LtS :: Lt m n -> Lt ('S m) ('S n)
data Le (m :: Nat) (n :: Nat) where
  LeZ :: Le 'Z n
  LeS :: Le m n -> Le ('S m) ('S n)

ltToSNat :: Lt m n -> SNat m
ltToSNat LtZ = SZ
ltToSNat (LtS pfLt) = SS $ ltToSNat pfLt

data BNat (n :: Nat) where
  BNat :: Lt m n -> BNat n

instance ToInt (BNat n) where
  toInt (BNat pfLt) = toInt $ ltToSNat pfLt
instance Show (BNat n) where
  show m = show $ toInt m

-- instances for BNat n
instance Eq (BNat n) where
  m1 == m2 = toInt m1 == toInt m2
instance Ord (BNat n) where
  m1 <= m2 = toInt m1 <= toInt m2

fromIntegerBNat :: SNat n -> Integer -> BNat n
fromIntegerBNat n m = 
  case fromInteger m of {SomeSNat m ->
  case compareSNat m n of
    Left pfLt -> BNat pfLt
    _         -> error $ "integer " ++ show m ++ " not less than bound " ++ show n
  }

instance KnownNat n => Num (BNat n) where
  m + n = undefined
  m - n = undefined
  m * n = undefined
  signum n = fromInteger 1 -- all nats are positive
  abs = undefined

  fromInteger m = fromIntegerBNat (sNat @n) m


-- find the range from m to n, inclusive
rangeSNat :: Lt m n -> Lt n p -> [BNat p]
rangeSNat LtZ pfLt = allBNat pfLt
rangeSNat (LtS pfLtmn) (LtS pfLtnp) = raise <$> rangeSNat pfLtmn pfLtnp

raise :: BNat p -> BNat ('S p)
raise (BNat pfLt) = BNat $ LtS pfLt

-- list all BNats <= n
allBNat :: Lt n p -> [BNat p]
allBNat LtZ        = [BNat LtZ]
allBNat (LtS pfLt) = BNat LtZ : (raise <$> allBNat pfLt)

compareSNat :: SNat m -> SNat n -> Either (Lt m n) (Le n m)
compareSNat SZ (SS _) = Left LtZ
compareSNat _  SZ     = Right LeZ
compareSNat (SS m) (SS n) = case compareSNat m n of
  Left  pfLt -> Left  $ LtS pfLt
  Right pfLe -> Right $ LeS pfLe

compareBNat :: Lt m1 n -> Lt m2 n -> Either (Lt m1 m2) (Le m2 m1)
compareBNat LtZ (LtS _) = Left LtZ
compareBNat (LtS _) LtZ = Right LeZ
compareBNat (LtS pfLt1) (LtS pfLt2) = 
  case compareBNat pfLt1 pfLt2 of
    Left  pfLt -> Left  $ LtS pfLt
    Right pfLe -> Right $ LeS pfLe

-- there are no nats less than 0
maxBNat :: SNat n -> BNat n
maxBNat SZ     = error "BNat 0 is uninhabited"
maxBNat (SS n) = BNat $ ltS n

ltS :: SNat n -> Lt n ('S n)
ltS SZ = LtZ
ltS (SS n) = LtS $ ltS n


instance Ix (BNat n) where
  range :: (BNat n, BNat n) -> [BNat n]
  range (BNat pfLt1, BNat pfLt2) = case compareBNat pfLt1 pfLt2 of
    Left pfLt -> rangeSNat pfLt pfLt2
    _         -> error $ "Ill-defined range " ++ show (BNat pfLt1, BNat pfLt2)

  index :: (BNat n, BNat n) -> BNat n -> Int
  index (m1,m2) m = index (toInt m1, toInt m2) $ toInt m

  inRange :: (BNat n, BNat n) -> BNat n -> Bool
  inRange (m1,m2) m = inRange (toInt m1, toInt m2) $ toInt m

type Vector n = Array (BNat n)

vector :: SNat n -> [a] -> Vector n a
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

