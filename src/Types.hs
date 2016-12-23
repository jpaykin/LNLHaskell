{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase
#-}

module Types where

import Data.Kind
import Data.Constraint

type EffectSig = * -> *
type TypeSig = * -> *
type Sig = (EffectSig, [TypeSig])
type family SigEffect (sig :: Sig) :: EffectSig where
  SigEffect '(m,_) = m
type family SigType (sig :: Sig) :: [TypeSig] where
  SigType '(_,tys) = tys


data LType (sig :: Sig) where
  Sig    :: InList ty (SigType sig) -> ty (LType sig) -> LType sig
  Lolli  :: LType sig -> LType sig -> LType sig

type (⊸) = Lolli
infixr 0 ⊸

{-
  One    :: LType sig
  Lower  :: * -> LType sig
  Tensor :: LType sig -> LType sig -> LType sig
  With   :: LType sig -> LType sig -> LType sig
  Plus   :: LType sig -> LType sig -> LType sig


type (⊗) = Tensor
infixr 3 ⊗

type (&) = With
infixr 3 &

type (⊕) = Plus
infixr 3 ⊕
-}

type Ident = Nat
data Usage sig = Used (LType sig) | Unused

data Ctx  sig = Empty | N (NCtx sig)
data NCtx sig = End (LType sig) | Cons (Usage sig) (NCtx sig)

-- In Lists ------------------------------------------------------

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

class CInSig (ty :: TypeSig) (sig :: Sig) where
  type PfInList :: InList ty (SigType sig)

compareInList :: InList x1 ls -> InList x2 ls 
              -> Maybe (Dict( x1 ~ x2 ))
compareInList = undefined

type family IsInList (ty :: a) (ls :: [a]) :: InList ty ls where
  IsInList ty (ty ': _)  = 'InList 'InZ
  IsInList ty (_  ': ls) = InListCons (IsInList ty ls)

type family InListCons (pf :: InList (x :: a) ls) :: InList x (y ': ls) where
  InListCons ('InList pfM) = 'InList ('InS pfM)

type Sig' (ty :: TypeSig) (tys :: [TypeSig]) = ('Sig (IsInList ty tys) 
            :: ty (LType '(m,tys)) -> LType '(m,tys))


-- Singleton types for contexts -----------------------------------


data SUsage :: Usage sig -> * where
  SUsed   :: forall s. SUsage ('Used s)
  SUnused :: SUsage 'Unused

data SCtx :: Ctx sig -> * where
  SEmpty  :: SCtx 'Empty
  SN      :: SNCtx g -> SCtx ('N g)
data SNCtx :: NCtx sig -> * where
  SEnd  :: SNCtx ('End t)
  SCons :: SUsage u -> SNCtx g -> SNCtx ('Cons u g)

-- Type families about contexts ---------------------------------

type family Add (x :: Ident) (s :: LType sig) (g :: Ctx sig) :: Ctx sig where
  Add x s g = 'N (AddN x s g)

type family AddN (x :: Ident) (s :: LType sig) (g :: Ctx sig) :: NCtx sig where
  AddN 'Z     s 'Empty = 'End s
  AddN ('S x) s 'Empty = 'Cons 'Unused (AddN x s 'Empty)
  AddN x      s ('N g) = AddNN x s g

type family AddNN x s (g :: NCtx sig) :: NCtx sig where
  AddNN ('S x) s ('End t)          = 'Cons ('Used t) (SingletonN x s)
  AddNN 'Z     s ('Cons 'Unused g) = 'Cons ('Used s) g
  AddNN ('S x) s ('Cons u       g) = 'Cons u (AddNN x s g)

type family ConsN (u :: Usage sig) (g :: Ctx sig) :: Ctx sig where
  ConsN ('Used s) 'Empty = 'N ('End s)
  ConsN 'Unused   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)

type family ConsN_partial u g :: NCtx sig where
  ConsN_partial ('Used s) 'Empty = 'End s
  ConsN_partial u         ('N g) = 'Cons u g

consN :: SUsage u -> SCtx g -> SCtx (ConsN u g) 
consN SUsed   SEmpty = SN $ SEnd 
consN SUnused SEmpty = SEmpty
consN u       (SN g) = SN $ SCons u g

type family SingletonN x (s :: LType sig) :: NCtx sig where
  SingletonN x s = AddN x s 'Empty
--  SingletonN 'Z     s = 'End s
--  SingletonN ('S x) s = 'Cons 'Unused (SingletonN x s)
type family Singleton x (s :: LType sig) :: Ctx sig where
--  Singleton x s = Add x s 'Empty
  Singleton x s = 'N (SingletonN x s)

type family Merge12 (g1 :: Ctx sig) (g2 :: Ctx sig) :: Ctx sig where
  Merge12 'Empty  'Empty  = 'Empty
  Merge12 'Empty  ('N g)  = 'N g
  Merge12 ('N g)  'Empty  = 'N g
  Merge12 ('N g1) ('N g2) = 'N (MergeN12 g1 g2)

type family MergeN12 (g1 :: NCtx sig) (g2 :: NCtx sig) :: NCtx sig where
  MergeN12 ('End s)           ('Cons 'Unused g2) = 'Cons ('Used s) g2
  MergeN12 ('Cons 'Unused g1) ('End s)           = 'Cons ('Used s) g1
  MergeN12 ('Cons u1 g1)      ('Cons u2 g2)      = 'Cons (MergeU12 u1 u2) (MergeN12 g1 g2)

type family MergeU12 u1 u2 :: Usage sig where
  MergeU12 'Unused   'Unused   = 'Unused
  MergeU12 ('Used s) 'Unused   = 'Used s
  MergeU12 'Unused   ('Used s) = 'Used s

type family RemoveN (x :: Ident) (g :: NCtx sig) :: Ctx sig where
  RemoveN 'Z     ('End s)            = 'Empty
  RemoveN 'Z     ('Cons ('Used s) g) = 'N ('Cons 'Unused g)
  RemoveN ('S x) ('Cons u g)         = ConsN u (RemoveN x g)

type family Remove (x :: Ident) (g :: Ctx sig) :: Ctx sig where
  Remove x ('N g) = RemoveN x g


-- Nats ---------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord)

data SIdent :: Nat -> * where
  SZ :: SIdent 'Z
  SS :: SIdent x -> SIdent ('S x)


instance Num Nat where
  Z   + n   = n
  S m + n   = S (m+n)
  Z   - n   = Z
  m   - Z   = m
  S m - S n = m - n
  Z   * n   = Z
  S m * n   = m * n + n
  abs e     = e
  signum e  = S Z
  fromInteger = undefined
  negate e    = undefined

toInt :: Nat -> Int
toInt Z = 0
toInt (S n) = toInt n + 1

instance Show Nat where
  show n = show $ toInt n
