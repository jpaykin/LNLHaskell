{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module GUI where

import Data.Kind

import Types
import Context
import Lang
import Interface
import Data.Singletons

data GUISig sig = WidgetSig
type Widget = (LType' sig 'WidgetSig :: LType sig)

data GUIExp :: Lang sig -> Ctx sig -> LType sig -> Type where
  Button  :: String -> GUIExp lang Empty Widget
  OnClick :: LExp lang γ Widget -> GUIExp lang γ (Widget ⊗ (Event @@ One))

data GUIVal :: Lang sig -> LType sig -> Type where

type GUIDom = '(GUIExp, GUIVal)

type HasGUIDom (lang :: Lang sig) = ( WFDomain GUIDom lang
                                    , WFDomain TensorDom lang, WFDomain OneDom lang
                                    , WFDomain LolliDom lang, WFDomain LowerDom lang
                                    , WFDomain PlusDom lang)

instance HasGUIDom lang => Domain GUIDom lang where
  evalDomain = undefined
instance Show (GUIExp lang γ σ) where
  show = undefined

button :: HasGUIDom lang => String -> Lift lang Widget
button s = Suspend $ dom @GUIDom $ Button s

onClick :: HasGUIDom lang => Lift lang (LState Widget (Event @@ One))
onClick = Suspend . λ $ \w -> dom @GUIDom (OnClick w)

data Event :: LType sig ~> LType sig
type instance Apply Event τ = (τ ⊸ Bot) ⊸ Bot


instance HasGUIDom lang => LFunctor lang Event where
  lfmap :: LExp lang 'Empty ((σ ⊸ τ) ⊸ ((σ ⊸ Bot) ⊸ Bot) ⊸ (τ ⊸ Bot) ⊸ Bot)
  lfmap = λ $ \f -> λ $ \e -> λ $ \k -> 
    e `app` (compose `app` k `app` f)

instance HasGUIDom lang => LApplicative lang Event where
  lpure :: LExp lang 'Empty (τ ⊸ (τ ⊸ Bot) ⊸ Bot)
  lpure = λ $ \t -> λ $ \k -> k `app` t
  llift :: LExp lang 'Empty ( Event @@ (σ ⊸ τ) ⊸ Event @@ σ ⊸ Event @@ τ)
  llift = λ $ \f' -> λ $ \s' -> λ $ \k -> 
    s' `app` (λ $ \s ->
    f' `app` (λ $ \f ->
    k `app` (f `app` s)))
instance HasGUIDom lang => LMonad lang Event where
  lbind :: LExp lang 'Empty (Event @@ σ ⊸ (σ ⊸ Event @@ τ) ⊸ Event @@ τ)
  lbind = λ $ \s' -> λ $ \f -> λ $ \k ->
    s' `app` (λ $ \s -> f `app` s `app` k)
