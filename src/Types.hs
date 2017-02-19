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

data LType where
  -- ty :: * -> *
  MkLType :: ty LType -> LType


type Exp = Ctx -> LType -> Type
type Val = LType -> Type
data Sig = Sig (Type -> Type) (Exp) (Val)

type family Effect (sig :: Sig) :: Type -> Type where
  Effect ('Sig m _ _) = m
type family LExp (sig :: Sig) :: Exp where
  LExp ('Sig _ exp _) = exp
type family LVal (sig :: Sig) :: Val where
  LVal ('Sig _ _ val) = val

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

type family SingletonN x (σ :: LType) :: NCtx where
  SingletonN x σ = AddN x σ 'Empty
type family Singleton x (σ :: LType) :: Ctx where
  Singleton x σ = 'N (SingletonN x σ)


type family Add (x :: Nat) (σ :: LType) (g :: Ctx) :: Ctx where
  Add x σ g = 'N (AddN x σ g)

type family AddN (x :: Nat) (σ :: LType) (g :: Ctx) :: NCtx where
  AddN 'Z     σ 'Empty = 'End σ
  AddN ('S x) σ 'Empty = 'Cons 'Nothing (AddN x σ 'Empty)
  AddN x      σ ('N g) = AddNN x σ g

type family AddNN x σ (g :: NCtx) :: NCtx where
  AddNN ('S x) σ ('End τ)          = 'Cons ('Just τ) (SingletonN x σ)
  AddNN 'Z     σ ('Cons 'Nothing g) = 'Cons ('Just σ) g
  AddNN ('S x) σ ('Cons u       g) = 'Cons u (AddNN x σ g)

type family Remove (x :: Nat) (g :: Ctx) :: Ctx where
  Remove x 'Empty = TypeError (Text "Cannot remove anything from an empty context")
  Remove x ('N γ) = RemoveN x γ
type family RemoveN (x :: Nat) (γ :: NCtx) :: Ctx where
  RemoveN 'Z ('End _) = 'Empty
  RemoveN 'Z ('Cons ('Just _) γ) = 'N ('Cons 'Nothing γ)
  RemoveN ('S x) ('Cons u γ)     = ConsN u (RemoveN x γ)

type family Merge12 (g1 :: Ctx) (g2 :: Ctx) :: Ctx where
  Merge12 'Empty 'Empty = 'Empty
  Merge12 'Empty ('N g2) = 'N g2
  Merge12 ('N g1) 'Empty = 'N g1
  Merge12 ('N g1) ('N g2) = 'N (Merge12N g1 g2)
type family Merge12N (g1 :: NCtx) (g2 :: NCtx) :: NCtx where
  Merge12N ('End σ) ('Cons 'Nothing g2) = 'Cons ('Just σ) g2
  Merge12N ('Cons 'Nothing g1) ('End σ) = 'Cons ('Just σ) g1
  Merge12N ('Cons 'Nothing g1) ('Cons 'Nothing g2) = 'Cons Nothing (Merge12N g1 g2)
  Merge12N ('Cons ('Just σ) g1) ('Cons 'Nothing g2) = 'Cons ('Just σ) (Merge12N g1 g2)
  Merge12N ('Cons 'Nothing g1) ('Cons ('Just σ) g2) = 'Cons ('Just σ) (Merge12N g1 g2)


