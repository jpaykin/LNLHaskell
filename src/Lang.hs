{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds
#-}

module Lang where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe
import Debug.Trace

import Prelim
import Types
import Context
import Proofs

----------------------------------------------------------------
-- Syntax ------------------------------------------------------
----------------------------------------------------------------

-- Linear expressions consist solely of variables, and constructors added from
-- different domains.
data LExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Var :: SingletonCtx x τ γ -> LExp lang γ τ
  Dom :: (Domain dom lang, Show (ExpDom dom lang γ τ))
      => Proxy dom 
      -> ExpDom dom lang γ τ
      -> LExp lang γ τ
-- TODO: Any way to write Dom @dom e 
--       instead of Dom (Proxy :: Proxy dom) e
--       or Dom @_ @dom e

-- Values are solely obtained from the domains
data LVal :: forall sig. Lang sig -> LType sig -> * where
  VDom  :: Domain dom lang
        => Proxy dom -> ValDom dom lang σ -> LVal lang σ

-- Domains and Languages
  
-- A domain of type Dom sig (paramaterized by a signature sig) is a pair of
-- types that extend the syntax of expressions and values respectively.
type Dom sig = (Lang sig -> Ctx sig -> LType sig -> *, Lang sig -> LType sig -> *)

-- ExpDom and ValDom are projections out of Dom sig
type family ExpDom (dom :: Dom sig) :: Lang sig -> Ctx sig -> LType sig -> * where
  ExpDom '(exp,val) = exp
type family ValDom (dom :: Dom sig) :: Lang sig -> LType sig -> * where
  ValDom '(exp,val) = val

-- RDom is a runtime representation of the domain
--data family RDom :: Dom sig -> * 





-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
newtype Lang sig = Lang [Dom sig]





-- A well-formed domain is one in which the effect of the signature is a monad,
-- and the domain appears in the language
type WFDomain (dom :: Dom sig) (lang :: Lang sig) = 
    (CInLang dom lang, Monad (SigEffect sig))

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
class WFDomain dom lang => Domain (dom :: Dom sig) (lang :: Lang sig) where
  evalDomain  :: ECtx lang g
              -> ExpDom dom lang g σ
              -> SigEffect sig (LVal lang σ)


type family FromLang (lang :: Lang sig) :: [Dom sig] where
   FromLang ('Lang lang) = lang
type CInLang dom lang = CInList dom (FromLang lang)


-- Evaluation Contexts ------------------------------------

type ECtx (lang :: Lang sig) = SCtx (LVal lang)


-- Evaluation ---------------------------------------------

eval :: forall sig (lang :: Lang sig) (g :: Ctx sig) (σ :: LType sig).
        Monad (SigEffect sig)
     => LExp lang 'Empty σ
     -> SigEffect sig (LVal lang σ)
eval = eval' SEmpty

eval' :: forall sig (lang :: Lang sig) (g :: Ctx sig) (σ :: LType sig).
        Monad (SigEffect sig)
     => ECtx lang g
     -> LExp lang g σ 
     -> SigEffect sig (LVal lang σ)
eval' ρ (Var pfS)                      = return $ lookup (singletonIn pfS) ρ
eval' ρ (Dom (proxy :: Proxy dom) e)   = evalDomain @sig @dom ρ e


------------------------------------------------------

fromLVal' :: forall sig dom (lang :: Lang sig) σ.
            CInLang dom lang
         => Proxy dom -> LVal lang σ -> Maybe (ValDom dom lang σ)
fromLVal' _ (VDom (proxy :: Proxy dom') v) = 
  case compareInList (pfInList @_ @dom) (pfInList @_ @dom' @(FromLang lang)) of
    Nothing   -> Nothing
    Just Dict -> Just v

fromLVal :: forall sig dom (lang :: Lang sig) σ.
            CInLang dom lang
         => Proxy dom -> LVal lang σ -> ValDom dom lang σ
fromLVal proxy = fromJust . fromLVal' proxy

-- this function is partial if the value is not
-- in the specified domain
evalToValDom :: forall sig dom (lang :: Lang sig) g σ.
                (CInLang dom lang, Monad (SigEffect sig))
             => Proxy dom -> ECtx lang g
             -> LExp lang g σ -> SigEffect sig (ValDom dom lang σ)
evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

instance Show (LExp lang γ t) where
  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
  show (Dom _ e) = show e

