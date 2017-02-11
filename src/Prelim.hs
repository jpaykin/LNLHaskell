{-# LANGUAGE TypeApplications, ScopedTypeVariables, TypeInType,
             TypeOperators, GADTs, TypeFamilies, UndecidableInstances,
             MultiParamTypeClasses, FlexibleInstances, AllowAmbiguousTypes,
             InstanceSigs, RankNTypes
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors #-}

module Prelim where

--import Data.Kind
import Data.Constraint
import Data.Array
--import GHC.TypeLits (TypeError, ErrorMessage(..))
import Data.Type.Equality
import Data.Singletons
import Unsafe.Coerce

--------------------------------------------
-- Nats ------------------------------------
--------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord)
--data SNat :: Nat -> * where
--  SZ :: SNat 'Z
--  SS :: SNat x -> SNat ('S x)
data instance Sing (x :: Nat) where
  SZ :: Sing Z
  SS :: Sing x -> Sing (S x)
instance SingI Z where
  sing = SZ
instance SingI x => SingI (S x) where
  sing = SS sing

{-
class KnownNat n where
  sNat :: SNat n
instance KnownNat 'Z where
  sNat = SZ
instance KnownNat n => KnownNat ('S n) where
  sNat = SS sNat
-}

type family EqNat (m :: Nat) (n :: Nat) :: Bool where
  EqNat Z     Z     = True
  EqNat (S m) (S n) = EqNat m n
  EqNat Z     (S n) = False
  EqNat (S m) Z     = False
type instance (m :: Nat) == (n :: Nat) = EqNat m n
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
type family RaiseTo (m :: Nat) (n :: Nat) :: Nat where
  m `RaiseTo` Z = S Z
  m `RaiseTo` S n = m `Times` (m `RaiseTo` n)

-- Some Nats
type One   = S Z
type Two   = S One
type Three = S Two
type Four  = S Three

one :: Sing One
one = SS SZ
two :: Sing Two
two = SS one
three :: Sing Three
three = SS two
four :: Sing Four
four = SS three

{-
type family Div (m :: Nat) (n :: Nat) :: Nat where
--  Div m n     = If (n == Z) (TypeError (Text "Division by zero"))
--               (If (n == (S Z)) m
--               (If (m < n) Z (S ((m `Minus` n) `Div` n))))
  Div _ Z     = TypeError (Text "Division by zero")
  Div m (S Z) = m
  Div m n     = If (m < n) Z (S ((m `Minus` n) `Div` n))
type family Mod (m :: Nat) (n :: Nat) :: Nat where
  Mod _ Z     = TypeError (Text "Modulo by zero")
  Mod _ (S Z) = Z
  Mod m n     = If (m < n) m ((m `Minus` n) `Mod` n)
-}

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t f = t
  If 'False t f = f


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

-- Proofs about nats
-- using unsafeCoerce for efficiency, but may uncomment out proofs to check typing

plus0r :: forall n. Sing n -> Dict (Plus n Z ~ n)
plus0r _ = unsafeCoerce (Dict :: Dict ())
--plus0r SZ = Dict
--plus0r (SS n) = case plus0r n of Dict -> Dict

plusSr :: Sing m -> Sing n -> Dict (Plus m (S n) ~ S (Plus m n))
plusSr _ _ = unsafeCoerce (Dict :: Dict ())
--plusSr SZ _ = Dict
--plusSr (SS m) n = case plusSr m n of Dict -> Dict

plusMinus :: (n < m) ~ False 
          => Sing m -> Sing n -> Dict (Plus m (Minus n m) ~ n)
plusMinus _ _ = unsafeCoerce (Dict :: Dict ())
--plusMinus SZ SZ = Dict
--plusMinus SZ (SS _) = Dict
--plusMinus (SS m) (SS n) = case plusMinus m n of Dict -> Dict

times1r :: forall n. Sing n -> Dict (Times n (S Z) ~ n)
times1r _ = unsafeCoerce (Dict :: Dict ())
--times1r SZ = Dict
--times1r (SS n) = case times1r n of Dict -> Dict

timesAssoc :: Sing m -> Sing n -> Sing p 
           -> Dict (Times m (Times n p) ~ Times (Times m n) p)
timesAssoc _ _ _ = unsafeCoerce (Dict :: Dict ())

timesSymm :: Sing m -> Sing n -> Dict (Times m n ~ Times n m)
timesSymm _ _ = unsafeCoerce (Dict :: Dict ())

-- really want SMT plugin here
raiseToPlus :: forall m n1 n2. Sing m -> Sing n1 -> Sing n2
                -> Dict (((m `RaiseTo` n1 ) `Times` (m `RaiseTo` n2) )
                        ~ (m `RaiseTo` (n1 `Plus` n2)))
raiseToPlus _ _ _ = unsafeCoerce (Dict :: Dict ())
{-
raiseToPlus m SZ n2 = case plus0r (raiseToSNat m n2) of Dict -> Dict
raiseToPlus m n1 SZ = case plus0r n1 of {Dict ->
                         case times1r (raiseToSNat m n1) of {Dict -> 
                         Dict }}
raiseToPlus m (SS n1) (SS n2) = 
  case plusSr n1 n2             of {Dict -> 
  case timesAssoc m mn1 (timesSNat m mn2) of {Dict -> 
  case timesAssoc mn1 m mn2     of {Dict -> 
  case timesSymm mn1 m          of {Dict ->
  case timesAssoc m mn1 mn2     of {Dict -> 
  case raiseToPlus m n1 n2   of {Dict -> 
    Dict
  }}}}}}
  where
    mn1 = raiseToSNat m n1
    mn2 = raiseToSNat m n2
-}

-- Operations on SNats

type SomeSNat = SomeSing Nat
{-
data SomeSNat where
  SomeSNat :: Sing n -> SomeSNat
-}
instance Eq (SomeSing Nat) where
  SomeSing m == SomeSing n = case eqSNat m n of 
    Left  Dict -> True
    Right Dict -> False
instance Ord (SomeSing Nat) where
  SomeSing m <= SomeSing n = 
    if SomeSing m == SomeSing n then True
    else case compareSNat m n of
      Left Dict  -> True
      Right Dict -> False
instance Show (SomeSing Nat) where
  show (SomeSing n) = show n

instance Num (SomeSing Nat) where
  SomeSing m + SomeSing n = SomeSing $ plusSNat m n
  SomeSing m - SomeSing n = SomeSing $ minusSNat m n
  SomeSing m * SomeSing n = SomeSing $ timesSNat m n
  abs n = n
  signum _ = 1
  
  fromInteger 0 = SomeSing SZ
  fromInteger n = case fromInteger (n-1) of
    SomeSing n' -> SomeSing $ SS n'

class ToInt a where
  toInt :: a -> Int

instance ToInt Nat where
  toInt Z = 0
  toInt (S n) = toInt n + 1
instance ToInt (Sing (n :: Nat)) where
  toInt n = toInt $ toNat n


instance Show Nat where
  show n = show $ toInt n

toNat :: forall (n :: Nat). Sing n -> Nat
toNat SZ = Z
toNat (SS n) = S $ toNat n

instance forall (n :: Nat). Show (Sing n) where
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
  BNat :: (m < n) ~ 'True => Sing m -> BNat n

instance ToInt (BNat n) where
  toInt (BNat m) = toInt m
instance Show (BNat n) where
  show (BNat m) = show m
instance Eq (BNat n) where
  m1 == m2 = toInt m1 == toInt m2
instance Ord (BNat n) where
  m1 <= m2 = toInt m1 <= toInt m2

compareSNat :: forall (m :: Nat) (n :: Nat). Sing m -> Sing n 
            -> Either (Dict (m < n ~ 'True)) (Dict ((m < n) ~ 'False))
compareSNat SZ SZ     = Right Dict
compareSNat SZ (SS _) = Left  Dict
compareSNat (SS _) SZ = Right Dict
compareSNat (SS m) (SS n) = case compareSNat m n of
    Left  Dict -> Left  Dict
    Right Dict -> Right Dict


eqSNat :: forall (m :: Nat) (n :: Nat). Sing m -> Sing n 
       -> Either (Dict (m~n, (m==n) ~ 'True)) (Dict ((m == n) ~ 'False))
eqSNat SZ SZ = Left Dict
eqSNat SZ (SS _) = Right Dict
eqSNat (SS _) SZ = Right Dict
eqSNat (SS m) (SS n) = case eqSNat m n of
    Left  Dict -> Left  Dict
    Right Dict -> Right Dict

fromIntegerBNat :: forall (n :: Nat). SingI n => Integer -> BNat n
fromIntegerBNat m = 
  case fromInteger m of {SomeSing m' -> 
  case compareSNat m' n of
           Left Dict -> BNat m'
           Right Dict -> error $ "Cannot construct BNat: " ++ show m ++ " not less than bound " ++ show n
  }
  where
    n = (sing :: Sing n)


bNat :: forall n. SingI n => SomeSing Nat -> BNat n
bNat (SomeSing m) = case compareSNat m (sing :: Sing n) of
           Left Dict -> BNat m
           Right Dict -> error $ "Cannot construct BNat: " ++ show m ++ " not less than bound " ++ show (sing :: Sing n)

ltS :: Sing x -> Dict (x < 'S x ~ 'True)
ltS SZ = Dict
ltS (SS x) = case ltS x of Dict -> Dict

succLtTrans :: 'S x < y ~ 'True => Sing x -> Sing y -> Dict (x < y ~ 'True)
succLtTrans SZ (SS _) = Dict
succLtTrans (SS x) (SS y) = case succLtTrans x y of Dict -> Dict

ltSTrans :: x < y ~ True => Sing x -> Sing y -> Dict (x < S y ~ True)
ltSTrans SZ     (SS _) = Dict
ltSTrans (SS x) (SS y) = case ltSTrans x y of Dict -> Dict

maxBNat :: Sing n -> BNat n
maxBNat SZ     = error "BNat 0 is uninhabited"
maxBNat (SS n) = case ltS n of Dict -> BNat n


boundBNat :: forall n (m :: Nat). SingI n => Sing m -> BNat n
boundBNat m = case compareSNat m (sing :: Sing n) of
  Left Dict -> BNat m
  Right _   -> maxBNat (sing :: Sing n)

plusSNat :: Sing m1 -> Sing m2 -> Sing (m1 `Plus` m2)
plusSNat SZ m2 = m2
plusSNat (SS m1) m2 = SS $ plusSNat m1 m2

minusSNat :: Sing m1 -> Sing m2 -> Sing (m1 `Minus` m2)
minusSNat m1 SZ = m1
minusSNat SZ _  = SZ
minusSNat (SS m1) (SS m2) = minusSNat m1 m2

timesSNat :: Sing m1 -> Sing m2 -> Sing (m1 `Times` m2)
timesSNat SZ _ = SZ
timesSNat (SS m1) m2 = m2 `plusSNat` timesSNat m1 m2

raiseToSNat :: Sing m -> Sing n -> Sing (m `RaiseTo` n)
raiseToSNat _ SZ = SS SZ
raiseToSNat m (SS n) = m `timesSNat` (m `raiseToSNat` n)


divSNat :: forall (m :: Nat) (n :: Nat). Sing m -> Sing n -> SomeSing Nat
divSNat m n = divSomeSing (SomeSing m) (SomeSing n)


divSomeSing :: SomeSing Nat -> SomeSing Nat -> SomeSing Nat
divSomeSing _ n | n == 0 = error "Division by zero"
divSomeSing m n | n == 1 = m
divSomeSing m n | m < n  = 0
divSomeSing m n | otherwise = 1 + ((m-n) `divSomeSing` n)



modSNat :: forall (m :: Nat) (n :: Nat). Sing m -> Sing n -> SomeSing Nat
modSNat m n = modSomeSing (SomeSing m) (SomeSing n)

modSomeSing :: SomeSing Nat -> SomeSing Nat -> SomeSing Nat
modSomeSing _ n | n == 0 = error "Modulo by zero"
modSomeSing _ n | n == 1 = 0
modSomeSing m n | m < n  = m
modSomeSing m n | otherwise = (m-n) `modSomeSing` n

instance SingI n => Num (BNat n) where
  BNat m1 + BNat m2 = boundBNat (m1 `plusSNat`  m2)
  BNat m1 - BNat m2 = boundBNat (m1 `minusSNat` m2)
  BNat m1 * BNat m2 = boundBNat (m1 `timesSNat` m2)
  signum _ = fromInteger 1 -- all nats are positive
  abs n = n

  fromInteger m = fromIntegerBNat m
instance SingI n => Real (BNat n) where
  toRational = fromIntegral . toInt
instance SingI n => Enum (BNat n) where
  toEnum = fromIntegral 
  fromEnum = toInt
instance SingI n => Integral (BNat n) where
  quotRem (BNat i) (BNat j) = (bNat $ divSNat i j, bNat $ modSNat i j)
  toInteger = fromIntegral . toInt 

raise :: Sing n -> BNat n -> BNat ('S n)
raise n (BNat m) = case ltSTrans m n of Dict -> BNat m

allBNat :: Sing n -> [BNat n]
allBNat SZ = []
allBNat (SS n) = (raise n <$> allBNat n) ++ [maxBNat $ SS n]

instance SingI n => Ix (BNat n) where
  range :: (BNat n, BNat n) -> [BNat n]
  range (BNat _, BNat _) = allBNat (sing :: Sing n)

  index :: (BNat n, BNat n) -> BNat n -> Int
  index (m1,m2) m = index (toInt m1, toInt m2) $ toInt m

  inRange :: (BNat n, BNat n) -> BNat n -> Bool
  inRange (m1,m2) m = inRange (toInt m1, toInt m2) $ toInt m
