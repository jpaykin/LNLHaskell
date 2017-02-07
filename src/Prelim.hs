{-# LANGUAGE TypeApplications, ScopedTypeVariables, TypeInType,
             TypeOperators, GADTs, TypeFamilies, UndecidableInstances,
             MultiParamTypeClasses, FlexibleInstances, AllowAmbiguousTypes,
             InstanceSigs
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Prelim where

import Data.Kind
import Data.Constraint
import Data.Array

--------------------------------------------
-- Nats ------------------------------------
--------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord)
data SNat :: Nat -> * where
  SZ :: SNat 'Z
  SS :: SNat x -> SNat ('S x)


class KnownNat n where
  sNat :: SNat n
instance KnownNat 'Z where
  sNat = SZ
instance KnownNat n => KnownNat ('S n) where
  sNat = SS sNat

type family Plus (m :: Nat) (n :: Nat) :: Nat where
  Plus 'Z     n = n
  Plus ('S m) n = 'S (Plus m n)
type family Minus (m :: Nat) (n :: Nat) :: Nat where
  Minus n 'Z = n
  Minus 'Z n = 'Z
  Minus ('S m) ('S n) = Minus m n
type family Times (m :: Nat) (n :: Nat) :: Nat where
  Times 'Z     n = 'Z
  Times ('S m) n = Plus n (Times m n)

instance Num Nat where
  Z   + n   = n
  S m + n   = S (m+n)
  Z   - _   = Z
  m   - Z   = m
  S m - S n = m - n
  Z   * _   = Z
  S m * n   = m * n + n
  abs e     = e
  signum _  = S Z

  fromInteger 0 = Z
  fromInteger n = S $ fromInteger (n-1)

  negate n = n
instance Real Nat where
  toRational = toRational . toInt
instance Enum Nat where
  toEnum   = fromInteger . fromIntegral
  fromEnum = toInt
instance Integral Nat where
  toInteger = fromIntegral . toInt
  quotRem m n = let (q,r) = quotRem (fromEnum m) (fromEnum n)
                in (toEnum q, toEnum r)

-- Operations on SNats

sTimes :: SNat m -> SNat n -> SNat (m `Times` n)
sTimes = undefined

data SomeSNat where
  SomeSNat :: SNat n -> SomeSNat

instance Num SomeSNat where
  (+) = undefined
  (-) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  
  fromInteger 0 = SomeSNat SZ
  fromInteger n = case fromInteger (n-1) of
    SomeSNat n' -> SomeSNat $ SS n'

class ToInt a where
  toInt :: a -> Int

instance ToInt Nat where
  toInt Z = 0
  toInt (S n) = toInt n + 1
instance ToInt (SNat n) where
  toInt n = toInt $ toNat n


instance Show Nat where
  show n = show $ toInt n

toNat :: SNat n -> Nat
toNat SZ = Z
toNat (SS n) = S $ toNat n

instance Show (SNat n) where
  show n = show $ toNat n

--------------------------------------------
-- Maps ------------------------------------
--------------------------------------------

data InMap (i :: Nat) (x :: a) (xs :: [a]) where
  InZ :: InMap 'Z a (a ': as)
  InS :: InMap i a as -> InMap ('S i) a (b ': as)

data InList (x :: a) (xs :: [a]) where
  InList :: InMap i x xs -> InList x xs

class MapsTo (i :: Nat) (x :: a) (xs :: [a]) where
  pfInMap :: InMap i x xs
instance MapsTo 'Z a (a ': as) where
  pfInMap = InZ
instance MapsTo i a as => MapsTo ('S i) a (b ': as) where
  pfInMap = InS pfInMap

class CInList (x :: a) (xs :: [a]) where
  pfInList :: InList x xs
instance MapsTo (GetIndex x xs) x xs => CInList x xs where
  pfInList = InList (pfInMap @_ @(GetIndex x xs))

type family GetIndex (x :: a) (xs :: [a]) where
  GetIndex x (x ': _) = 'Z
  GetIndex x (_ ': ls) = 'S (GetIndex x ls)

compareInList :: InList x1 ls -> InList x2 ls 
              -> Maybe (Dict( x1 ~ x2 ))
compareInList (InList pfM1) (InList pfM2) = compareInMap pfM1 pfM2

compareInMap :: InMap i1 x1 ls -> InMap i2 x2 ls
             -> Maybe (Dict ( x1 ~ x2 ))
compareInMap InZ InZ = Just Dict
compareInMap (InS pfM1) (InS pfM2) = compareInMap pfM1 pfM2
compareInMap _ _ = Nothing

type family IsInList (ty :: a) (ls :: [a]) :: InList ty ls where
  IsInList ty (ty ': _)  = 'InList 'InZ
  IsInList ty (_  ': ls) = InListCons (IsInList ty ls)

type family InListCons (pf :: InList (x :: a) ls) :: InList x (y ': ls) where
  InListCons ('InList pfM) = 'InList ('InS pfM)

-- Bounded Natural Numbers

type family (<) (m :: Nat) (n :: Nat) :: Bool where
  'Z   < 'S n = 'True
  _    < 'Z   = 'False
  'S m < 'S n = m < n

data BNat (n :: Nat) where
  BNat :: (m < n) ~ 'True => SNat m -> BNat n

instance ToInt (BNat n) where
  toInt (BNat m) = toInt m
instance Show (BNat n) where
  show (BNat m) = show m
instance Eq (BNat n) where
  m1 == m2 = toInt m1 == toInt m2
instance Ord (BNat n) where
  m1 <= m2 = toInt m1 <= toInt m2

compareSNat :: SNat m -> SNat n 
            -> Either (Dict (m < n ~ 'True)) (Dict ((n < m) ~ 'False))
compareSNat = undefined

fromIntegerBNat :: SNat n -> Integer -> BNat n
fromIntegerBNat n m = 
  case fromInteger m of {SomeSNat m' ->
  case compareSNat m' n of
    Left Dict -> BNat m'
    Right Dict -> error $ "Integer " ++ show m ++ " not less than bound " ++ show n
  }

ltS :: SNat x -> Dict (x < 'S x ~ 'True)
ltS SZ = Dict
ltS (SS x) = case ltS x of Dict -> Dict

succLtTrans :: 'S x < y ~ 'True => SNat x -> SNat y -> Dict (x < y ~ 'True)
succLtTrans SZ (SS _) = Dict
succLtTrans (SS x) (SS y) = case succLtTrans x y of Dict -> Dict

maxBNat :: SNat n -> BNat n
maxBNat SZ     = error "BNat 0 is uninhabited"
maxBNat (SS n) = case ltS n of Dict -> BNat n


boundBNat :: forall n m. KnownNat n => SNat m -> BNat n
boundBNat m = case compareSNat m (sNat @n) of
  Left Dict -> BNat m
  Right _   -> maxBNat $ sNat @n

plusSNat :: SNat m1 -> SNat m2 -> SNat (m1 `Plus` m2)
plusSNat SZ m2 = m2
plusSNat (SS m1) m2 = SS $ plusSNat m1 m2

minusSNat :: SNat m1 -> SNat m2 -> SNat (m1 `Minus` m2)
minusSNat m1 SZ = m1
minusSNat SZ _  = SZ
minusSNat (SS m1) (SS m2) = minusSNat m1 m2

timesSNat :: SNat m1 -> SNat m2 -> SNat (m1 `Times` m2)
timesSNat SZ _ = SZ
timesSNat (SS m1) m2 = m2 `plusSNat` timesSNat m1 m2

instance KnownNat n => Num (BNat n) where
  BNat m1 + BNat m2 = boundBNat (m1 `plusSNat`  m2)
  BNat m1 - BNat m2 = boundBNat (m1 `minusSNat` m2)
  BNat m1 * BNat m2 = boundBNat (m1 `timesSNat` m2)
  signum _ = fromInteger 1 -- all nats are positive
  abs = undefined

  fromInteger m = fromIntegerBNat (sNat @n) m
instance KnownNat n => Real (BNat n) where
  toRational = fromIntegral . toInt
instance KnownNat n => Enum (BNat n) where
  toEnum = fromIntegral 
  fromEnum = toInt
instance KnownNat n => Integral (BNat n) where
  quotRem = undefined
  toInteger = fromIntegral . toInt 

raise :: BNat n -> BNat ('S n)
raise = undefined

allBNat :: SNat n -> [BNat n]
allBNat SZ = []
allBNat (SS n) = BNat SZ : (raise <$> allBNat n)

instance KnownNat n => Ix (BNat n) where
  range :: (BNat n, BNat n) -> [BNat n]
  range (BNat _, BNat _) = allBNat $ sNat @n

  index :: (BNat n, BNat n) -> BNat n -> Int
  index (m1,m2) m = index (toInt m1, toInt m2) $ toInt m

  inRange :: (BNat n, BNat n) -> BNat n -> Bool
  inRange (m1,m2) m = inRange (toInt m1, toInt m2) $ toInt m
