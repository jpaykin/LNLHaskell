{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Context where

import Data.Kind

import Prelim
import Types

data Usage sig = Used (LType sig) | Unused

data Ctx  sig = Empty | N (NCtx sig)
data NCtx sig = End (LType sig) | Cons (Usage sig) (NCtx sig)

-- Singleton types for contexts -----------------------------------

-- Singleton contexts are paramaterized by some data (LType sig -> *)
-- which itself is paramaterized by some linear type.
data SCtx :: (LType sig -> *) -> Ctx sig -> * where
  SEmpty  :: SCtx dat 'Empty
  SN      :: SNCtx dat g -> SCtx dat ('N g)

data SNCtx :: (LType sig -> *) -> NCtx sig -> * where
  SEnd  :: dat t -> SNCtx dat ('End t)
  SCons :: SUsage dat u -> SNCtx dat g -> SNCtx dat ('Cons u g)

data SUsage :: forall sig. (LType sig -> *) -> Usage sig -> * where
  SUsed   :: forall s dat. dat s -> SUsage dat ('Used s)
  SUnused :: SUsage dat 'Unused

data Phantom t = Phantom


----------------------------------------------------------
-- Relations about contexts ------------------------------
----------------------------------------------------------

-- Add To Context ----------------------------------------------

data AddNCtxN :: Nat -> LType sig -> NCtx sig -> NCtx sig -> * where
  AddHere  :: SNCtx Phantom g -> AddNCtxN 'Z s ('Cons 'Unused g) ('Cons ('Used s) g)
  AddEnd   :: SingletonNCtx x s g  -> AddNCtxN ('S x) s ('End t) ('Cons ('Used t) g)
  AddLater :: SUsage Phantom u -> AddNCtxN x s g g'
           -> AddNCtxN ('S x) s ('Cons u g) ('Cons u g')

data AddCtxN :: Nat -> LType sig -> Ctx sig -> NCtx sig -> * where
  AddS       :: SingletonNCtx x s g -> AddCtxN x s 'Empty g
  AddNN      :: AddNCtxN x s g g' -> AddCtxN x s ('N g) g'

data AddCtx  :: Nat -> LType sig -> Ctx sig -> Ctx sig -> * where
  AddN :: AddCtxN x s g g' -> AddCtx x s g ('N g')


-- Singleton Context ------------------------------------------

data SingletonNCtx :: Nat -> LType sig -> NCtx sig -> * where
  AddHereS  :: SingletonNCtx 'Z s ('End s)
  AddLaterS :: SingletonNCtx x s g -> SingletonNCtx ('S x) s ('Cons 'Unused g)

data SingletonCtx :: Nat -> LType sig -> Ctx sig -> * where
  SingN :: SingletonNCtx x s g -> SingletonCtx x s ('N g)

-- Merge ----------------------------------------------------

data MergeU :: Usage sig -> Usage sig -> Usage sig -> * where
  MergeUn :: MergeU 'Unused   'Unused   'Unused
  MergeUL :: MergeU ('Used s) 'Unused   ('Used s)
  MergeUR :: MergeU 'Unused   ('Used s) ('Used s)

data Merge :: Ctx sig -> Ctx sig -> Ctx sig -> * where
  MergeE  :: Merge 'Empty 'Empty 'Empty
  MergeEL :: SNCtx Phantom g -> Merge 'Empty ('N g) ('N g)
  MergeER :: SNCtx Phantom g -> Merge ('N g) 'Empty ('N g)
  MergeN  :: MergeN g1 g2 g3 -> Merge ('N g1) ('N g2) ('N g3)

data MergeN :: NCtx sig -> NCtx sig -> NCtx sig -> * where
  MergeEndL :: SNCtx Phantom g2 -> MergeN ('End s) ('Cons 'Unused g2) ('Cons ('Used s) g2)
  MergeEndR :: SNCtx Phantom g1 -> MergeN ('Cons 'Unused g1) ('End s) ('Cons ('Used s) g1)
  MergeCons :: MergeU u1 u2 u3 -> MergeN g1 g2 g3 
            -> MergeN ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3)


-- In -------------------------------

data InN :: Nat -> LType sig -> NCtx sig -> * where
  InEnd   :: InN 'Z s ('End s)
  InHere  :: SNCtx Phantom g    -> InN 'Z s ('Cons ('Used s) g)
  InLater :: SUsage Phantom u   -> InN x s g  -> InN ('S x) s ('Cons u g)

data In :: Nat -> LType sig -> Ctx sig -> * where
  In :: InN x s g -> In x s ('N g)

-- Div -----------------------------------------------

data Div :: Ctx sig -> Ctx sig -> Ctx sig -> * where
  DivEmpty :: SCtx Phantom g -> Div g 'Empty g
  DivN     :: DivN g1 g2 g3 -> Div ('N g1) ('N g2) g3

data DivN       :: NCtx sig -> NCtx sig -> Ctx sig -> * where
  DivEndEnd     :: DivN ('End s) ('End s) 'Empty
  DivConsEnd    :: SNCtx Phantom g -> DivN ('Cons ('Used s) g) ('End s) ('N ('Cons 'Unused g))
  DivConsCons   :: DivN g1 g2 g3 
                -> MergeU u3 u2 u1
                -> DivN ('Cons u1 g1) ('Cons u2 g2) (ConsN u3 g3)



-------------------------------------------------------------
-- Type families --------------------------------------------
-------------------------------------------------------------


-- Fresh variables ------------------------------------------

type family FreshN (g :: NCtx sig) :: Nat where
  FreshN ('End t)            = 'S 'Z
  FreshN ('Cons 'Unused g)   = 'Z
  FreshN ('Cons ('Used s) g) = 'S (FreshN g)

type family Fresh (g::Ctx sig) :: Nat where
  Fresh 'Empty = 'Z
  Fresh ('N g) = FreshN g

type family FreshN2 g :: Nat where
  FreshN2 ('End t)           = 'S ('S 'Z)
  FreshN2 ('Cons 'Unused g)   = 'S (FreshN g)
  FreshN2 ('Cons ('Used s) g) = 'S (FreshN2 g)


type family Fresh2 (g::Ctx sig) :: Nat where
  Fresh2 'Empty = 'S 'Z
  Fresh2 ('N g) = FreshN2 g

-- Add Ctx ---------------------------------------------------


type family Add (x :: Nat) (s :: LType sig) (g :: Ctx sig) :: Ctx sig where
  Add x s g = 'N (AddN x s g)

type family AddN (x :: Nat) (s :: LType sig) (g :: Ctx sig) :: NCtx sig where
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

-- Singleton contexts ---------------------

type family SingletonN x (s :: LType sig) :: NCtx sig where
  SingletonN x s = AddN x s 'Empty
type family Singleton x (s :: LType sig) :: Ctx sig where
  Singleton x s = 'N (SingletonN x s)

-- Merge contexts --------------------------

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

