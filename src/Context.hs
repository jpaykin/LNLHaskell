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


-- Singleton types for contexts -----------------------------------

-- Singleton contexts are paramaterized by some data (LType sig -> *)
-- which itself is paramaterized by some linear type.

{-
data SCtx :: (LType sig -> *) -> Ctx sig -> * where
  SEmpty  :: SCtx dat 'Empty
  SN      :: SNCtx dat g -> SCtx dat ('N g)

data SNCtx :: (LType sig -> *) -> NCtx sig -> * where
  SEnd  :: dat τ -> SNCtx dat ('End τ)
  SCons :: SMaybe dat u -> SNCtx dat g -> SNCtx dat ('Cons u g)

data SMaybe :: forall sig. (LType sig -> *) -> Maybe (LType sig) -> * where
  SJust   :: forall σ dat. dat σ -> SMaybe dat ('Just σ)
  SNothing :: SMaybe dat 'Nothing

data Phantom τ = Phantom
-}

----------------------------------------------------------
-- Relations about contexts ------------------------------
----------------------------------------------------------

-- Add To Context ----------------------------------------------

data AddNCtxN :: Nat -> LType sig -> NCtx sig -> NCtx sig -> * where
  AddHere  :: NCtxVal g 
           -> AddNCtxN 'Z σ ('Cons 'Nothing g) ('Cons ('Just σ) g)
  AddEnd   :: SingletonNCtx x σ g  
           -> AddNCtxN ('S x) σ ('End τ) ('Cons ('Just τ) g)
  AddLater :: MaybeVal u -> AddNCtxN x σ g g'
           -> AddNCtxN ('S x) σ ('Cons u g) ('Cons u g')

data AddCtxN :: Nat -> LType sig -> Ctx sig -> NCtx sig -> * where
  AddS       :: SingletonNCtx x σ g -> AddCtxN x σ 'Empty g
  AddNN      :: AddNCtxN x σ g g' -> AddCtxN x σ ('N g) g'

data AddCtx  :: Nat -> LType sig -> Ctx sig -> Ctx sig -> * where
  AddN :: AddCtxN x σ g g' -> AddCtx x σ g ('N g')


-- Singleton Context ------------------------------------------

data SingletonNCtx :: Nat -> LType sig -> NCtx sig -> * where
  AddHereS  :: SingletonNCtx 'Z σ ('End σ)
  AddLaterS :: SingletonNCtx x σ g -> SingletonNCtx ('S x) σ ('Cons 'Nothing g)

data SingletonCtx :: Nat -> LType sig -> Ctx sig -> * where
  SingN :: SingletonNCtx x σ g -> SingletonCtx x σ ('N g)

instance ToInt (SingletonNCtx x s g) where
  toInt AddHereS = 0
  toInt (AddLaterS pfS) = 1+toInt pfS
instance Show (SingletonCtx x s g) where
  show (SingN pfS) = "x" ++ show (toInt pfS)

  

-- Merge ----------------------------------------------------

data MergeU :: Maybe (LType sig) -> Maybe (LType sig) -> Maybe (LType sig) -> * where
  MergeUn :: MergeU 'Nothing   'Nothing   'Nothing
  MergeUL :: MergeU ('Just σ) 'Nothing   ('Just σ)
  MergeUR :: MergeU 'Nothing   ('Just σ) ('Just σ)

data Merge :: Ctx sig -> Ctx sig -> Ctx sig -> * where
  MergeE  :: Merge 'Empty 'Empty 'Empty
  MergeEL :: NCtxVal g -> Merge 'Empty ('N g) ('N g)
  MergeER :: NCtxVal g -> Merge ('N g) 'Empty ('N g)
  MergeN  :: MergeN g1 g2 g3 -> Merge ('N g1) ('N g2) ('N g3)

data MergeN :: NCtx sig -> NCtx sig -> NCtx sig -> * where
  MergeEndL :: NCtxVal g2 
            -> MergeN ('End σ) ('Cons 'Nothing g2) ('Cons ('Just σ) g2)
  MergeEndR :: NCtxVal g1 
            -> MergeN ('Cons 'Nothing g1) ('End σ) ('Cons ('Just σ) g1)
  MergeCons :: MergeU u1 u2 u3 -> MergeN g1 g2 g3 
            -> MergeN ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3)


-- In -------------------------------

data InN :: Nat -> LType sig -> NCtx sig -> * where
  InEnd   :: InN 'Z σ ('End σ)
  InHere  :: NCtxVal g    -> InN 'Z σ ('Cons ('Just σ) g)
  InLater :: MaybeVal u   -> InN x σ g  -> InN ('S x) σ ('Cons u g)

data In :: Nat -> LType sig -> Ctx sig -> * where
  In :: InN x σ g -> In x σ ('N g)

instance Show (In x σ γ) where
  show (In pfI) = "x" ++ show (toInt pfI)
instance ToInt (InN x s γ) where
  toInt InEnd = 0
  toInt (InHere _) = 0
  toInt (InLater _ pfI) = 1 + toInt pfI


-------------------------------------------------------------
-- Type families --------------------------------------------
-------------------------------------------------------------



-- Add Ctx ---------------------------------------------------


type family Add (x :: Nat) (σ :: LType sig) (g :: Ctx sig) :: Ctx sig where
  Add x σ g = 'N (AddN x σ g)

type family AddN (x :: Nat) (σ :: LType sig) (g :: Ctx sig) :: NCtx sig where
  AddN 'Z     σ 'Empty = 'End σ
  AddN ('S x) σ 'Empty = 'Cons 'Nothing (AddN x σ 'Empty)
  AddN x      σ ('N g) = AddNN x σ g

type family AddNN x σ (g :: NCtx sig) :: NCtx sig where
  AddNN ('S x) σ ('End τ)          = 'Cons ('Just τ) (SingletonN x σ)
  AddNN 'Z     σ ('Cons 'Nothing g) = 'Cons ('Just σ) g
  AddNN ('S x) σ ('Cons u       g) = 'Cons u (AddNN x σ g)


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
  MergeN12 ('End σ)           ('Cons 'Nothing g2) = 'Cons ('Just σ) g2
  MergeN12 ('Cons 'Nothing g1) ('End σ)           = 'Cons ('Just σ) g1
  MergeN12 ('Cons u1 g1)      ('Cons u2 g2)      = 'Cons (MergeU12 u1 u2) (MergeN12 g1 g2)

type family MergeU12 u1 u2 :: Maybe (LType sig) where
  MergeU12 'Nothing   'Nothing   = 'Nothing
  MergeU12 ('Just σ) 'Nothing   = 'Just σ
  MergeU12 'Nothing   ('Just σ) = 'Just σ
