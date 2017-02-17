{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts
#-}

module Types where

import Prelim

import Data.Kind
import GHC.TypeLits (TypeError, ErrorMessage(..))


data LType (sig :: Sig) where
  -- ty :: * -> *
  LType :: InSig ty sig -> ty (LType sig) -> LType sig

-- Example of such a ty :: Sig -> *:
-- 
-- data LolliSig sig = LolliSig (LType sig) (LType sig)
-- 
-- type (⊸) (σ :: LType sig) (τ :: LType sig) = LType' sig ('LolliSig σ τ)
-- infixr 0 ⊸


-- We can get around providing the proof that ty is in the signature
type MkLType sig (σ :: ty (LType sig)) = 'LType (IsInSig ty sig) σ






-- A signature consists of a monad (in which evaluation will occur) and a list
-- of type constructors. This way, a signature can be extended
-- semlessly by adding a new type constructor to the signature.
-- A type constructor (of type Sig -> *) is a way to extend the syntax of LTypes.
-- e.g. 
--      data LolliSig sig = LolliSig (LType sig) (LType sig)
type Sig = (Type -> Type, [Type -> Type])
--data Sig = Sig (Type -> Type) [Type -> Type]

-- SigEffect and SigType project out the monad and constructors, respectively
-- (Sig should be a type level record)
type family SigEffect (sig :: Sig) :: Type -> Type where
  SigEffect '(m,_) = m
type family SigType (sig :: Sig) :: [Type -> Type] where
  SigType '(_,tys) = tys








-- In lists ------------------------------------------------------

type InSig ty sig = InList ty (SigType sig)

-- Type class that searches for a proof that ty is a type constructor in sig
class CInSig (ty :: Type -> Type) (sig :: Sig)
instance CInSig' (GetIndex ty (SigType sig)) ty sig => CInSig ty sig

class CInSig' (i :: Nat) (ty :: Type -> Type) (sig :: Sig)
instance CInSig' 'Z ty '(m,ty ': tys)
instance CInSig' i  ty '(m,tys) => CInSig' ('S i) ty '(m,ty' ': tys)

-- The type InSig ty sig computes a type-level proof that ty ∈ sig
-- (if it exists)
type IsInSig (ty :: Type -> Type) sig = 
    (IsInList ty (SigType sig) :: InList ty (SigType sig))


-- Values are extensible, used for implementation
type family LVal (σ :: LType sig) :: Type

data Ctx  sig = Empty | N (NCtx sig)
data NCtx sig = End (LType sig) | Cons (Maybe (LType sig)) (NCtx sig)

type family CtxVal (γ :: Ctx sig) :: Type where
  CtxVal Empty = ()
  CtxVal (N γ) = NCtxVal γ
type family NCtxVal (γ :: NCtx sig) :: Type where
  NCtxVal (End σ)           = LVal σ
  NCtxVal (Cons Nothing γ)  = NCtxVal γ
  NCtxVal (Cons (Just σ) γ) = (LVal σ, NCtxVal γ)
type family MaybeVal (u :: Maybe (LType sig)) :: Type where
  MaybeVal 'Nothing  = ()
  MaybeVal ('Just σ) = LVal σ

type family ConsN (u :: Maybe (LType sig)) (g :: Ctx sig) :: Ctx sig where
  ConsN ('Just σ) 'Empty = 'N ('End σ)
  ConsN 'Nothing   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)


-- Fresh variables ------------------------------------------

type family FreshN (g :: NCtx sig) :: Nat where
  FreshN ('End τ)            = 'S 'Z
  FreshN ('Cons 'Nothing g)   = 'Z
  FreshN ('Cons ('Just σ) g) = 'S (FreshN g)

type family Fresh (g::Ctx sig) :: Nat where
  Fresh 'Empty = 'Z
  Fresh ('N g) = FreshN g

type family FreshN2 g :: Nat where
  FreshN2 ('End τ)           = 'S ('S 'Z)
  FreshN2 ('Cons 'Nothing g)   = 'S (FreshN g)
  FreshN2 ('Cons ('Just σ) g) = 'S (FreshN2 g)


type family Fresh2 (g::Ctx sig) :: Nat where
  Fresh2 'Empty = 'S 'Z
  Fresh2 ('N g) = FreshN2 g

type family AddFresh γ σ where
  AddFresh 'Empty σ = 'N ('End σ)
  AddFresh ('N γ) σ = 'N (AddFreshN γ σ)
type family AddFreshN γ σ where
  AddFreshN ('End τ)            σ = 'Cons ('Just τ) ('End σ)
  AddFreshN ('Cons 'Nothing γ)  σ = 'Cons ('Just σ) γ
  AddFreshN ('Cons ('Just τ) γ) σ = 'Cons ('Just τ) (AddFreshN γ σ)

type family Div (γ :: Ctx sig) (γ0 :: Ctx sig) = (r :: Ctx sig) where
--  Div γ γ = 'Empty
  Div γ 'Empty = γ
  Div ('N γ) ('N γ0) = DivN γ γ0
  Div γ      γ0      = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

type family DivN (γ :: NCtx sig) (γ0 :: NCtx sig) = (r :: Ctx sig) where
  DivN ('End _)            ('End _)             = 'Empty
  DivN ('Cons ('Just _) γ) ('End _)             = 'N ('Cons 'Nothing γ)
  DivN ('Cons ('Just _) γ) ('Cons ('Just _) γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN ('Cons ('Just σ) γ) ('Cons 'Nothing γ0)  = ConsN ('Just σ) (DivN γ γ0)
  DivN ('Cons 'Nothing  γ) ('Cons 'Nothing  γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN γ                   γ0                   = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

-- Instances ----------------------------------------- 

type Exp sig = Ctx sig -> LType sig -> Type
class Eval (exp :: Exp sig) where
  eval :: Monad (SigEffect sig) => exp γ τ -> CtxVal γ -> SigEffect sig (LVal τ)


-- Deep embedding found in Lang.hs
