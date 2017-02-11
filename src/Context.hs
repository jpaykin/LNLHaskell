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
  SEnd  :: dat τ -> SNCtx dat ('End τ)
  SCons :: SUsage dat u -> SNCtx dat g -> SNCtx dat ('Cons u g)

data SUsage :: forall sig. (LType sig -> *) -> Usage sig -> * where
  SUsed   :: forall σ dat. dat σ -> SUsage dat ('Used σ)
  SUnused :: SUsage dat 'Unused

data Phantom τ = Phantom

----------------------------------------------------------
-- Relations about contexts ------------------------------
----------------------------------------------------------

-- Add To Context ----------------------------------------------

data AddNCtxN :: Nat -> LType sig -> NCtx sig -> NCtx sig -> * where
  AddHere  :: SNCtx Phantom g 
           -> AddNCtxN 'Z σ ('Cons 'Unused g) ('Cons ('Used σ) g)
  AddEnd   :: SingletonNCtx x σ g  
           -> AddNCtxN ('S x) σ ('End τ) ('Cons ('Used τ) g)
  AddLater :: SUsage Phantom u -> AddNCtxN x σ g g'
           -> AddNCtxN ('S x) σ ('Cons u g) ('Cons u g')

data AddCtxN :: Nat -> LType sig -> Ctx sig -> NCtx sig -> * where
  AddS       :: SingletonNCtx x σ g -> AddCtxN x σ 'Empty g
  AddNN      :: AddNCtxN x σ g g' -> AddCtxN x σ ('N g) g'

data AddCtx  :: Nat -> LType sig -> Ctx sig -> Ctx sig -> * where
  AddN :: AddCtxN x σ g g' -> AddCtx x σ g ('N g')


-- Singleton Context ------------------------------------------

data SingletonNCtx :: Nat -> LType sig -> NCtx sig -> * where
  AddHereS  :: SingletonNCtx 'Z σ ('End σ)
  AddLaterS :: SingletonNCtx x σ g -> SingletonNCtx ('S x) σ ('Cons 'Unused g)

data SingletonCtx :: Nat -> LType sig -> Ctx sig -> * where
  SingN :: SingletonNCtx x σ g -> SingletonCtx x σ ('N g)

instance ToInt (SingletonNCtx x s g) where
  toInt AddHereS = 0
  toInt (AddLaterS pfS) = 1+toInt pfS
instance Show (SingletonCtx x s g) where
  show (SingN pfS) = "x" ++ show (toInt pfS)

  

-- Merge ----------------------------------------------------

data MergeU :: Usage sig -> Usage sig -> Usage sig -> * where
  MergeUn :: MergeU 'Unused   'Unused   'Unused
  MergeUL :: MergeU ('Used σ) 'Unused   ('Used σ)
  MergeUR :: MergeU 'Unused   ('Used σ) ('Used σ)

data Merge :: Ctx sig -> Ctx sig -> Ctx sig -> * where
  MergeE  :: Merge 'Empty 'Empty 'Empty
  MergeEL :: SNCtx Phantom g -> Merge 'Empty ('N g) ('N g)
  MergeER :: SNCtx Phantom g -> Merge ('N g) 'Empty ('N g)
  MergeN  :: MergeN g1 g2 g3 -> Merge ('N g1) ('N g2) ('N g3)

data MergeN :: NCtx sig -> NCtx sig -> NCtx sig -> * where
  MergeEndL :: SNCtx Phantom g2 
            -> MergeN ('End σ) ('Cons 'Unused g2) ('Cons ('Used σ) g2)
  MergeEndR :: SNCtx Phantom g1 
            -> MergeN ('Cons 'Unused g1) ('End σ) ('Cons ('Used σ) g1)
  MergeCons :: MergeU u1 u2 u3 -> MergeN g1 g2 g3 
            -> MergeN ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3)


-- In -------------------------------

data InN :: Nat -> LType sig -> NCtx sig -> * where
  InEnd   :: InN 'Z σ ('End σ)
  InHere  :: SNCtx Phantom g    -> InN 'Z σ ('Cons ('Used σ) g)
  InLater :: SUsage Phantom u   -> InN x σ g  -> InN ('S x) σ ('Cons u g)

data In :: Nat -> LType sig -> Ctx sig -> * where
  In :: InN x σ g -> In x σ ('N g)

instance Show (In x σ γ) where
  show (In pfI) = "x" ++ show (toInt pfI)
instance ToInt (InN x s γ) where
  toInt InEnd = 0
  toInt (InHere _) = 0
  toInt (InLater _ pfI) = 1 + toInt pfI


-- Div -----------------------------------------------

data Div :: Ctx sig -> Ctx sig -> Ctx sig -> * where
  DivEmpty :: SCtx Phantom g -> Div g 'Empty g
  DivN     :: DivN g1 g2 g3 -> Div ('N g1) ('N g2) g3

data DivN       :: NCtx sig -> NCtx sig -> Ctx sig -> * where
  DivEndEnd     :: DivN ('End σ) ('End σ) 'Empty
  DivConsEnd    :: SNCtx Phantom g 
                -> DivN ('Cons ('Used σ) g) ('End σ) ('N ('Cons 'Unused g))
  DivConsCons   :: DivN g1 g2 g3 
                -> MergeU u3 u2 u1
                -> DivN ('Cons u1 g1) ('Cons u2 g2) (ConsN u3 g3)



-------------------------------------------------------------
-- Type families --------------------------------------------
-------------------------------------------------------------


-- Fresh variables ------------------------------------------

type family FreshN (g :: NCtx sig) :: Nat where
  FreshN ('End τ)            = 'S 'Z
  FreshN ('Cons 'Unused g)   = 'Z
  FreshN ('Cons ('Used σ) g) = 'S (FreshN g)

type family Fresh (g::Ctx sig) :: Nat where
  Fresh 'Empty = 'Z
  Fresh ('N g) = FreshN g

type family FreshN2 g :: Nat where
  FreshN2 ('End τ)           = 'S ('S 'Z)
  FreshN2 ('Cons 'Unused g)   = 'S (FreshN g)
  FreshN2 ('Cons ('Used σ) g) = 'S (FreshN2 g)


type family Fresh2 (g::Ctx sig) :: Nat where
  Fresh2 'Empty = 'S 'Z
  Fresh2 ('N g) = FreshN2 g

-- Add Ctx ---------------------------------------------------


type family Add (x :: Nat) (σ :: LType sig) (g :: Ctx sig) :: Ctx sig where
  Add x σ g = 'N (AddN x σ g)

type family AddN (x :: Nat) (σ :: LType sig) (g :: Ctx sig) :: NCtx sig where
  AddN 'Z     σ 'Empty = 'End σ
  AddN ('S x) σ 'Empty = 'Cons 'Unused (AddN x σ 'Empty)
  AddN x      σ ('N g) = AddNN x σ g

type family AddNN x σ (g :: NCtx sig) :: NCtx sig where
  AddNN ('S x) σ ('End τ)          = 'Cons ('Used τ) (SingletonN x σ)
  AddNN 'Z     σ ('Cons 'Unused g) = 'Cons ('Used σ) g
  AddNN ('S x) σ ('Cons u       g) = 'Cons u (AddNN x σ g)

type family ConsN (u :: Usage sig) (g :: Ctx sig) :: Ctx sig where
  ConsN ('Used σ) 'Empty = 'N ('End σ)
  ConsN 'Unused   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)

-- Singleton contexts ---------------------

type family SingletonN x (σ :: LType sig) :: NCtx sig where
  SingletonN x σ = AddN x σ 'Empty
type family Singleton x (σ :: LType sig) :: Ctx sig where
  Singleton x σ = 'N (SingletonN x σ)

-- Merge contexts --------------------------

type family Merge12 (g1 :: Ctx sig) (g2 :: Ctx sig) :: Ctx sig where
  Merge12 'Empty  'Empty  = 'Empty
  Merge12 'Empty  ('N g)  = 'N g
  Merge12 ('N g)  'Empty  = 'N g
  Merge12 ('N g1) ('N g2) = 'N (MergeN12 g1 g2)

type family MergeN12 (g1 :: NCtx sig) (g2 :: NCtx sig) :: NCtx sig where
  MergeN12 ('End σ)           ('Cons 'Unused g2) = 'Cons ('Used σ) g2
  MergeN12 ('Cons 'Unused g1) ('End σ)           = 'Cons ('Used σ) g1
  MergeN12 ('Cons u1 g1)      ('Cons u2 g2)      = 'Cons (MergeU12 u1 u2) (MergeN12 g1 g2)

type family MergeU12 u1 u2 :: Usage sig where
  MergeU12 'Unused   'Unused   = 'Unused
  MergeU12 ('Used σ) 'Unused   = 'Used σ
  MergeU12 'Unused   ('Used σ) = 'Used σ
