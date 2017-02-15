{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             TypeFamilyDependencies
#-}

module Tagless where
 
import Prelude hiding ((^))
import Prelim
import Types
import Context
import Classes

import Data.Kind





data LolliSig sig where
  LolliSig :: LType sig -> LType sig -> LolliSig sig
type (⊸) (σ :: LType sig) (τ :: LType sig) = LType' sig ('LolliSig σ τ)
infixr 0 ⊸

class HasLolli (exp :: Ctx sig -> LType sig -> *) where
  λ :: (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (exp γ'' σ -> exp γ' τ) -> exp γ (σ ⊸ τ)
  (^) :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ) -> exp γ2 σ -> exp γ τ

data LowerSig sig where 
  LowerSig :: Type -> LowerSig sig
type Lower a = (LType' sig ('LowerSig a) :: LType sig)

class HasLower (exp :: Ctx sig -> LType sig -> *) where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ

data Lift (exp :: Ctx sig -> LType sig -> *) (τ :: LType sig) where
  Suspend :: exp 'Empty τ -> Lift exp τ

force :: Lift exp τ -> exp 'Empty τ
force (Suspend e) = e

id :: HasLolli exp => Lift exp (σ ⊸ σ)
id = Suspend . λ $ \x -> x

sApp :: HasLolli exp => Lift exp (σ ⊸ τ) -> Lift exp σ -> Lift exp τ
sApp f e = Suspend $ force  f ^ force e

--compose :: (HasLolli exp,CMerge γ1 γ2 γ)
--        => exp γ1 (τ ⊸ ρ) -> exp γ2 (σ ⊸ τ) -> exp γ (σ ⊸ ρ)
--compose g f = λ $ \x -> g ^ (f ^ x)

type family Val (σ :: LType sig) -- = r | r -> σ

type instance Val ('LType _ ('LolliSig σ τ)) = Val σ -> Val τ
type instance Val ('LType _ ('LowerSig a)) = a

class Eval (m :: * -> *) 
           (exp :: Ctx sig -> LType sig -> *) where
  eval :: Monad m => exp Empty τ -> m (Val τ)


type family CtxVal (γ :: Ctx sig) where
  CtxVal 'Empty                  = ()
  CtxVal ('N ('End σ))           = Val σ
  CtxVal ('N ('Cons 'Unused γ))  = CtxVal ('N γ)
--  CtxVal ('N ('Cons ('Used σ) γ) = (Val σ, CtxVal ('N γ))

data LExp γ τ where
  LExp :: (CtxVal γ -> Val τ) -> LExp γ τ

instance Eval m LExp where
  eval (LExp f) = return $ f ()

--instance HasLolli LExp where
--  λ f = LExp $ \
