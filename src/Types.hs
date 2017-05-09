{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, TypeFamilyDependencies
#-}

module Types where

import Prelim

import Data.Kind
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Data.Proxy

data LType where MkLType :: ty LType -> LType
  -- ty :: * -> *

type Sig = Type
type Exp = Ctx -> LType -> Type
type Val = LType -> Type

data family LExp (sig :: Sig) :: Exp
data family LVal (sig :: Sig) :: Val
type family Effect (sig :: Sig) :: Type -> Type


data Ctx  = Empty | N (NCtx)
data NCtx = End (LType) | Cons (Maybe (LType)) (NCtx)

data SCtx sig (γ :: Ctx) where
  SEmpty :: SCtx sig Empty
  SN     :: SNCtx sig γ -> SCtx sig (N γ)
data SNCtx sig (γ :: NCtx) where
  SEnd   :: LVal sig σ   -> SNCtx sig (End σ)
  SCons  :: SMaybe sig u -> SNCtx sig γ -> SNCtx sig ('Cons u γ)
data SMaybe sig (u :: Maybe LType) where
  SNothing :: SMaybe sig 'Nothing
  SJust    :: LVal sig σ -> SMaybe sig ('Just σ)


type family ConsN (u :: Maybe (LType)) (g :: Ctx) :: Ctx where
  ConsN ('Just σ) 'Empty = 'N ('End σ)
  ConsN 'Nothing   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)


-- Fresh variables ------------------------------------------

type family FreshN (g :: NCtx) :: Nat where
  FreshN ('End τ)            = 'S 'Z
  FreshN ('Cons 'Nothing g)   = 'Z
  FreshN ('Cons ('Just σ) g) = 'S (FreshN g)

type family Fresh (g::Ctx) :: Nat where
  Fresh 'Empty = 'Z
  Fresh ('N g) = FreshN g

type family FreshN2 g :: Nat where
  FreshN2 ('End τ)           = 'S ('S 'Z)
  FreshN2 ('Cons 'Nothing g)   = 'S (FreshN g)
  FreshN2 ('Cons ('Just σ) g) = 'S (FreshN2 g)

type family Fresh2 (g::Ctx) :: Nat where
  Fresh2 'Empty = 'S 'Z
  Fresh2 ('N g) = FreshN2 g


-- Type families

type family Div (γ :: Ctx) (γ0 :: Ctx) = (r :: Ctx) where
--  Div γ γ = 'Empty
  Div γ 'Empty = γ
  Div ('N γ) ('N γ0) = DivN γ γ0
  Div γ      γ0      = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

type family DivN (γ :: NCtx) (γ0 :: NCtx) = (r :: Ctx) where
  DivN ('End _)            ('End _)             = 'Empty
  DivN ('Cons ('Just _) γ) ('End _)             = 'N ('Cons 'Nothing γ)
  DivN ('Cons ('Just _) γ) ('Cons ('Just _) γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN ('Cons ('Just σ) γ) ('Cons 'Nothing γ0)  = ConsN ('Just σ) (DivN γ γ0)
  DivN ('Cons 'Nothing  γ) ('Cons 'Nothing  γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN γ                   γ0                   = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

type family SingletonNF x (σ :: LType) :: NCtx where
  SingletonNF x σ = AddNF x σ 'Empty
type family SingletonF x (σ :: LType) :: Ctx where
  SingletonF x σ = 'N (SingletonNF x σ)


type family AddF (x :: Nat) (σ :: LType) (g :: Ctx) :: Ctx where
  AddF x σ g = 'N (AddNF x σ g)

type family AddNF (x :: Nat) (σ :: LType) (g :: Ctx) :: NCtx where
  AddNF 'Z     σ 'Empty = 'End σ
  AddNF ('S x) σ 'Empty = 'Cons 'Nothing (AddNF x σ 'Empty)
  AddNF x      σ ('N g) = AddNNF x σ g

type family AddNNF x σ (g :: NCtx) :: NCtx where
  AddNNF ('S x) σ ('End τ)          = 'Cons ('Just τ) (SingletonNF x σ)
  AddNNF 'Z     σ ('Cons 'Nothing g) = 'Cons ('Just σ) g
  AddNNF ('S x) σ ('Cons u       g) = 'Cons u (AddNNF x σ g)

type family Remove (x :: Nat) (g :: Ctx) :: Ctx where
  Remove x 'Empty = TypeError (Text "Cannot remove anything from an empty context")
  Remove x ('N γ) = RemoveN x γ
type family RemoveN (x :: Nat) (γ :: NCtx) :: Ctx where
  RemoveN 'Z ('End _) = 'Empty
  RemoveN 'Z ('Cons ('Just _) γ) = 'N ('Cons 'Nothing γ)
  RemoveN ('S x) ('Cons u γ)     = ConsN u (RemoveN x γ)

type family MergeF (g1 :: Ctx) (g2 :: Ctx) :: Ctx where
  MergeF 'Empty 'Empty = 'Empty
  MergeF 'Empty ('N g2) = 'N g2
  MergeF ('N g1) 'Empty = 'N g1
  MergeF ('N g1) ('N g2) = 'N (MergeNF g1 g2)
type family MergeNF (g1 :: NCtx) (g2 :: NCtx) :: NCtx where
  MergeNF ('End σ) ('Cons 'Nothing g2) = 'Cons ('Just σ) g2
  MergeNF ('Cons 'Nothing g1) ('End σ) = 'Cons ('Just σ) g1
  MergeNF ('Cons 'Nothing g1) ('Cons 'Nothing g2) = 'Cons Nothing (MergeNF g1 g2)
  MergeNF ('Cons ('Just σ) g1) ('Cons 'Nothing g2) = 'Cons ('Just σ) (MergeNF g1 g2)
  MergeNF ('Cons 'Nothing g1) ('Cons ('Just σ) g2) = 'Cons ('Just σ) (MergeNF g1 g2)


