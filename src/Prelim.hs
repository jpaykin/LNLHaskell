{-# LANGUAGE TypeApplications, ScopedTypeVariables, TypeInType,
             TypeOperators, GADTs, TypeFamilies, UndecidableInstances,
             MultiParamTypeClasses, FlexibleInstances, AllowAmbiguousTypes,
             InstanceSigs, RankNTypes, ConstraintKinds
#-}
--{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors #-}

module Prelim where

--import Data.Kind
import Data.Constraint
import Data.Array
--import GHC.TypeLits (TypeError, ErrorMessage(..))
import GHC.TypeLits
import Data.Type.Equality
import Data.Singletons
import Unsafe.Coerce

--------------------------------------------
-- Nats ------------------------------------
--------------------------------------------

{-
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
-}

-- Some Nats
type One   = 1
type Two   = 2
type Three = 3
type Four  = 4


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

{-
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
-}

type S n = 1 + n

plus0r :: forall n. Sing n -> Dict ((n + 0) ~ n)
plus0r _ = unsafeCoerce (Dict :: Dict ())
--plus0r SZ = Dict
--plus0r (SS n) = case plus0r n of Dict -> Dict

plusSr :: Sing m -> Sing n -> Dict ((m + S n) ~ S (m + n))
plusSr _ _ = unsafeCoerce (Dict :: Dict ())
--plusSr SZ _ = Dict
--plusSr (SS m) n = case plusSr m n of Dict -> Dict

plusMinus :: (n < m)
          => Sing m -> Sing n -> Dict ((m + (n - m)) ~ n)
plusMinus _ _ = unsafeCoerce (Dict :: Dict ())
--plusMinus SZ SZ = Dict
--plusMinus SZ (SS _) = Dict
--plusMinus (SS m) (SS n) = case plusMinus m n of Dict -> Dict

times1r :: forall n. Sing n -> Dict ((n * 1) ~ n)
times1r _ = unsafeCoerce (Dict :: Dict ())
--times1r SZ = Dict
--times1r (SS n) = case times1r n of Dict -> Dict

timesAssoc :: Sing m -> Sing n -> Sing p 
           -> Dict ((m*(n*p)) ~ ((m*n)*p))
timesAssoc _ _ _ = unsafeCoerce (Dict :: Dict ())

timesSymm :: Sing m -> Sing n -> Dict ((m*n) ~ (n*m))
timesSymm _ _ = unsafeCoerce (Dict :: Dict ())

-- really want SMT plugin here
raiseToPlus :: forall m n1 n2. Sing m -> Sing n1 -> Sing n2
                -> Dict (((m^n1 )*(m^n2) )
                        ~ (m^(n1+n2)))
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

-}



--------------------------------------------
-- Pairs -----------------------------------
--------------------------------------------

type family Fst (pair :: (k1,k2)) :: k1 where
  Fst '(fst,_) = fst
type family Snd pair where
  Snd '(_,snd) = snd

--------------------------------------------
-- Maps ------------------------------------
--------------------------------------------

{-
data InMap (i :: Nat) (x :: a) (xs :: [a]) where
  InZ :: InMap 0 a (a ': as)
  InS :: InMap i a as -> InMap (S i) a (b ': as)

data InList (x :: a) (xs :: [a]) where
  InList :: InMap i x xs -> InList x xs

class MapsTo (i :: Nat) (x :: a) (xs :: [a]) where
  pfInMap :: InMap i x xs
instance MapsTo 0 a (a ': as) where
  pfInMap = InZ
instance MapsTo i a as => MapsTo (S i) a (b ': as) where
  pfInMap = InS pfInMap

class CInList (x :: a) (xs :: [a]) where
  pfInList :: InList x xs
instance MapsTo (GetIndex x xs) x xs => CInList x xs where
  pfInList = InList (pfInMap @_ @(GetIndex x xs))

type family GetIndex (x :: a) (xs :: [a]) where
  GetIndex x (x ': _)  = 0
  GetIndex x (_ ': ls) = S (GetIndex x ls)

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
-}

type x < y = CmpNat x y ~ LT

ltS :: forall x. KnownNat x => Dict (x < S x)
ltS = undefined
--ltS = case sameNat (Proxy :: Proxy x) (Proxy :: Proxy 0) of
--        Just Refl -> Dict
--        Nothing   -> case ltS @(x-1) of Dict -> Dict
--ltS x = case ltS x of Dict -> Dict

{-
succLtTrans :: 'S x < y ~ 'True => Sing x -> Sing y -> Dict (x < y ~ 'True)
succLtTrans SZ (SS _) = Dict
succLtTrans (SS x) (SS y) = case succLtTrans x y of Dict -> Dict

ltTrans :: forall x y z. (x < y ~ True, y < z ~ True) => Dict (x < z ~ True)
ltTrans = unsafeCoerce (Dict :: Dict ())

ltTwoRaiseTo :: forall n. Dict ((n < (Two `RaiseTo` n)) ~ True)
ltTwoRaiseTo = undefined

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
-}

