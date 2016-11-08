{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase
#-}

module Types where

import Data.Kind
import Data.Constraint


data LType where
  One    :: LType
  Lolli  :: LType -> LType -> LType
  Lower  :: * -> LType
  Tensor :: LType -> LType -> LType
  With   :: LType -> LType -> LType
  Plus   :: LType -> LType -> LType

type (⊸) = Lolli
infixr 0 ⊸

type (⊗) = Tensor
infixr 3 ⊗

type (&) = With
infixr 3 &

type (⊕) = Plus
infixr 3 ⊕


type Ident = Nat
data Usage = Used LType | Unused

data Ctx  = Empty | N NCtx
data NCtx = End LType | Cons Usage NCtx


-- Singleton types for contexts -----------------------------------


data SUsage :: Usage -> * where
  SUsed   :: forall s. SUsage ('Used s)
  SUnused :: SUsage 'Unused

data SCtx :: Ctx -> * where
  SEmpty  :: SCtx 'Empty
  SN      :: SNCtx g -> SCtx ('N g)
data SNCtx :: NCtx -> * where
  SEnd  :: SNCtx ('End t)
  SCons :: SUsage u -> SNCtx g -> SNCtx ('Cons u g)

-- Type families about contexts ---------------------------------

type family Add (x :: Ident) (s :: LType) (g :: Ctx) :: Ctx where
  Add x s g = 'N (AddN x s g)

type family AddN (x :: Ident) (s :: LType) (g :: Ctx) :: NCtx where
  AddN 'Z     s 'Empty = 'End s
  AddN ('S x) s 'Empty = 'Cons 'Unused (AddN x s 'Empty)
  AddN x      s ('N g) = AddNN x s g

type family AddNN x s (g :: NCtx) :: NCtx where
  AddNN ('S x) s ('End t)          = 'Cons ('Used t) (SingletonN x s)
  AddNN 'Z     s ('Cons 'Unused g) = 'Cons ('Used s) g
  AddNN ('S x) s ('Cons u       g) = 'Cons u (AddNN x s g)

type family ConsN (u :: Usage) (g :: Ctx) :: Ctx where
  ConsN ('Used s) 'Empty = 'N ('End s)
  ConsN 'Unused   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)

type family ConsN_partial u g :: NCtx where
  ConsN_partial ('Used s) 'Empty = 'End s
  ConsN_partial u         ('N g) = 'Cons u g

consN :: SUsage u -> SCtx g -> SCtx (ConsN u g) 
consN SUsed   SEmpty = SN $ SEnd 
consN SUnused SEmpty = SEmpty
consN u       (SN g) = SN $ SCons u g

type family SingletonN x s :: NCtx where
  SingletonN 'Z     s = 'End s
  SingletonN ('S x) s = 'Cons 'Unused (SingletonN x s)
type family Singleton x s :: Ctx where
  Singleton x s = 'N (SingletonN x s)

type family Merge12 (g1 :: Ctx) (g2 :: Ctx) :: Ctx where
  Merge12 'Empty  'Empty  = 'Empty
  Merge12 'Empty  ('N g)  = 'N g
  Merge12 ('N g)  'Empty  = 'N g
  Merge12 ('N g1) ('N g2) = 'N (MergeN12 g1 g2)

type family MergeN12 (g1 :: NCtx) (g2 :: NCtx) :: NCtx where
  MergeN12 ('End s)           ('Cons 'Unused g2) = 'Cons ('Used s) g2
  MergeN12 ('Cons 'Unused g1) ('End s)           = 'Cons ('Used s) g1
  MergeN12 ('Cons u1 g1)      ('Cons u2 g2)      = 'Cons (MergeU12 u1 u2) (MergeN12 g1 g2)

type family MergeU12 u1 u2 :: Usage where
  MergeU12 'Unused   'Unused   = 'Unused
  MergeU12 ('Used s) 'Unused   = 'Used s
  MergeU12 'Unused   ('Used s) = 'Used s

type family RemoveN (x :: Ident) (g :: NCtx) :: Ctx where
  RemoveN 'Z     ('End s)            = 'Empty
  RemoveN 'Z     ('Cons ('Used s) g) = 'N ('Cons 'Unused g)
  RemoveN ('S x) ('Cons u g)         = ConsN u (RemoveN x g)

type family Remove (x :: Ident) (g :: Ctx) :: Ctx where
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
