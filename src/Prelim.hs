{-# LANGUAGE TypeApplications, ScopedTypeVariables, TypeInType,
             TypeOperators, GADTs, TypeFamilies, UndecidableInstances,
             MultiParamTypeClasses, FlexibleInstances
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Prelim where

import Data.Kind
import Data.Constraint

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

