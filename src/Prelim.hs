--{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors #-}

module Prelim where

--import Data.Kind
import Data.Constraint
-- import GHC.TypeLits (TypeError, ErrorMessage(..))
import GHC.TypeLits
import Data.Type.Equality
-- import Data.Singletons 
-- import Data.Singletons.Prelude.Eq
import Unsafe.Coerce
import Data.Proxy (Proxy(..))

--------------------------------------------
-- Nats ------------------------------------
--------------------------------------------



eqSNat :: (KnownNat m, KnownNat n)
       => proxy m -> proxy' n
       -> Either (Dict (m ~ n
                       , (m == n) ~ True, (n == m) ~ True
                       , CmpNat m n ~ EQ, CmpNat n m ~ EQ))
                 (Dict ((m == n) ~ False, (n == m) ~ False))
eqSNat x y = if natVal x == natVal y 
             then Left  $ unsafeCoerce (Dict :: Dict ((),(),(),(),()))
             else Right $ unsafeCoerce (Dict :: Dict ((),()))

type CLT m n = (( (m == n) ~ False, (n == m) ~ False, CmpNat m n ~ LT, CmpNat n m ~ GT) :: Constraint)
type CEQ m n = (( m ~ n, (m == n) ~ True, (n == m) ~ True, CmpNat m n ~ EQ, CmpNat n m ~ EQ) :: Constraint)
type CGT m n = (((m == n) ~ False, (n == m) ~ False, CmpNat m n ~ GT, CmpNat n m ~ LT) :: Constraint)

data COrdering m n where
  CLT :: Dict (CLT m n) -> COrdering m n
  CEQ :: Dict (CEQ m n) -> COrdering m n
  CGT :: Dict (CGT m n) -> COrdering m n

unsafeCLT :: COrdering m n
unsafeCLT = CLT $ unsafeCoerce (Dict :: Dict ((),(),(),()))

unsafeCEQ :: COrdering m n
unsafeCEQ = CEQ $ unsafeCoerce (Dict :: Dict ((),(),(),(),()))

unsafeCGT :: COrdering m n
unsafeCGT = CGT $ unsafeCoerce (Dict :: Dict ((),(),(),()))


cmpNat :: (KnownNat m, KnownNat n)
       => proxy m -> proxy' n
       -> COrdering m n
cmpNat x y = case compare (natVal x) (natVal y) of
               LT -> unsafeCLT
               EQ -> unsafeCEQ    
               GT -> unsafeCGT



-- Some Nats
type One   = 1
type Two   = 2
type Three = 3
type Four  = 4

knownInt :: forall n. KnownNat n => Int
knownInt = fromIntegral $ natVal (Proxy :: Proxy n)


--------------------------------------------
-- Comparisons -----------------------------
--------------------------------------------


type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If True  t f = t
  If False t f = f

type family CompareOrd (ord :: Ordering) (lt :: α) (eq :: α) (gt :: α) :: α where
  CompareOrd LT lt eq gt = lt
  CompareOrd EQ lt eq gt = eq
  CompareOrd GT lt eq gt = gt

type family (x :: Nat) ==? (y :: Nat) :: Bool where
  x ==? y = CompareOrd (CmpNat x y) False True False

type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max x y = CompareOrd (CmpNat x y) y y x

type x < y = CmpNat x y ~ LT


--------------------------------------------
-- Pairs -----------------------------------
--------------------------------------------

type family Fst (pair :: (k1,k2)) :: k1 where
  Fst '(fst,_) = fst
type family Snd pair where
  Snd '(_,snd) = snd

