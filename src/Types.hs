{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, TypeFamilyDependencies
           , RankNTypes
#-}

module Types where

import Prelim

import Data.Kind
import GHC.TypeLits
import Data.Proxy
import Data.Singletons
import Data.Constraint

data LType where MkLType :: ty LType -> LType
  -- ty :: * -> *

type Sig = Type
type Exp = Ctx -> LType -> Type
type Val = LType -> Type

data family LExp (sig :: Sig) :: Exp
data family LVal (sig :: Sig) :: Val
type family Effect (sig :: Sig) :: Type -> Type

type Ctx = [(Nat,LType)]
--data Ctx  = Empty | N (NCtx)
--data NCtx = End (Nat,LType) | Cons (Maybe (Nat,LType)) (NCtx)

data instance Sing (γ :: Ctx) where
  SSEmpty :: Sing []
  SSCons  :: Sing u -> Sing γ -> Sing (u:γ)
data instance Sing (m :: Maybe α) where
  SSNothing :: Sing Nothing
  SSJust    :: Sing (Just a) -- cuts off
instance SingI [] where sing = SSEmpty
instance (SingI u, SingI γ) => SingI (u:γ) where sing = SSCons sing
instance SingI Nothing  where sing = SSNothing
instance SingI (Just a) where sing = SSJust

data SCtx sig (γ :: Ctx) where
  SEmpty :: SCtx sig []
  SCons  :: SMaybe sig u -> SCtx sig γ -> SCtx sig (u:γ)
data SMaybe sig (u :: Maybe (Nat,LType)) where
  SNothing :: SMaybe sig Nothing
  SJust    :: KnownNat x => LVal sig σ -> SMaybe sig (Just '(x,σ))

-- Define an evaluation context that may have extra entries, which makes
-- splitting a context a no-op, increasing performance.

data ECtx sig γ where
  ECtx :: (forall x σ. Dict (Lookup γ x ~ Just σ) -> Sing x -> LVal sig σ) 
       -> ECtx sig γ

eEmpty :: ECtx sig []
eEmpty = ECtx (\d x -> case d of)



-- Fresh variables ------------------------------------------

type family Fresh (g::Ctx) :: Nat where
  Fresh [] = 0
--  Fresh ((x,_):γ) = Max x (Fresh γ)


-- Type families

type family Lookup (γ :: Ctx) (x :: Nat) :: Maybe LType where
  Lookup [] _     = Nothing
  Lookup ('(x,σ):_) x = Just σ
  Lookup (_:γ)      x = Lookup γ x
  

type family Div (γ :: Ctx) (γ0 :: Ctx) = (r :: Ctx) where
  Div γ      'Empty = γ
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
  AddNF 0     σ 'Empty = 'End σ
  AddNF x σ 'Empty = 'Cons 'Nothing (AddNF (x-1) σ 'Empty)
  AddNF x      σ ('N g) = AddNNF x σ g

type family AddNNF x σ (g :: NCtx) :: NCtx where
  AddNNF x σ ('End τ)          = 'Cons ('Just τ) (SingletonNF (x-1) σ)
  AddNNF 0 σ ('Cons 'Nothing g) = 'Cons ('Just σ) g
  AddNNF x σ ('Cons u       g) = 'Cons u (AddNNF (x-1) σ g)

type family Remove (x :: Nat) (g :: Ctx) :: Ctx where
  Remove x 'Empty = TypeError (Text "Cannot remove anything from an empty context")
  Remove x ('N γ) = RemoveN x γ
type family RemoveN (x :: Nat) (γ :: NCtx) :: Ctx where
  RemoveN 0 ('End _) = 'Empty
  RemoveN 0 ('Cons ('Just _) γ) = 'N ('Cons 'Nothing γ)
  RemoveN x ('Cons u γ)     = ConsN u (RemoveN (x-1) γ)

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
