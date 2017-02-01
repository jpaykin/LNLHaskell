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
  Var :: SingletonCtx x t g -> LExp lang g t
  Dom :: (Domain dom lang, Show (ExpDom dom lang g t))
      => Proxy dom 
      -> ExpDom dom lang g t 
      -> LExp lang g t

-- Values are solely obtained from the domains
data LVal :: forall sig. Lang sig -> LType sig -> * where
  VDom  :: Domain dom lang
        => Proxy dom -> ValDom dom lang s -> LVal lang s

instance Show (LExp lang g t) where
  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
  show (Dom _ e) = show e

-- Domains and Languages
  
-- A domain of type Dom sig (paramaterized by a signature sig) is a pair of
-- types that extend the syntax of expressions and values respectively.
type Dom sig = (Lang sig -> Ctx sig -> LType sig -> *, Lang sig -> LType sig -> *)

-- ExpDom and ValDom are projections out of Dom sig
type family ExpDom (dom :: Dom sig) :: Lang sig -> Ctx sig -> LType sig -> * where
  ExpDom '(exp,val) = exp
type family ValDom (dom :: Dom sig) :: Lang sig -> LType sig -> * where
  ValDom '(exp,val) = val

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
              -> ExpDom dom lang g s
              -> SigEffect sig (LVal lang s)


type family FromLang (lang :: Lang sig) :: [Dom sig] where
   FromLang ('Lang lang) = lang
type CInLang dom lang = CInList dom (FromLang lang)


-- Evaluation Contexts ------------------------------------

-- Evaluation contexts map variables to either values or closures of
-- expressions. They are paramaterized by a typing context, which specifies the
-- domain of the context.
type ECtx (lang :: Lang sig) = SCtx (Data lang)

data Data (lang :: Lang sig) (s :: LType sig) where
  ValData :: LVal lang s -> Data lang s
  ExpData :: ECtx lang g -> LExp lang g s -> Data lang s

-- Evaluation ---------------------------------------------

eval :: forall sig (lang :: Lang sig) (g :: Ctx sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp lang 'Empty s 
     -> SigEffect sig (LVal lang s)
eval = eval' SEmpty

eval' :: forall sig (lang :: Lang sig) (g :: Ctx sig) (s :: LType sig).
        Monad (SigEffect sig)
     => ECtx lang g
     -> LExp lang g s 
     -> SigEffect sig (LVal lang s)
eval' ρ (Var pfS)                      = 
  case lookup (singletonIn pfS) ρ of
    ExpData ρ e -> eval' ρ e
    ValData v   -> return v
eval' ρ (Dom (proxy :: Proxy dom) e)   = trace (show e) $ evalDomain @sig @dom ρ e


------------------------------------------------------

fromLVal :: forall sig dom (lang :: Lang sig) s.
            CInLang dom lang
         => Proxy dom -> LVal lang s -> Maybe (ValDom dom lang s)
fromLVal _ (VDom (proxy :: Proxy dom') v) =
  case compareInList (pfInList @_ @dom) (pfInList @_ @dom' @(FromLang lang)) of
    Nothing   -> Nothing
    Just Dict -> Just v

-- this function is partial if the value is not
-- in the specified domain
evalToValDom :: forall sig dom (lang :: Lang sig) g s.
                (CInLang dom lang, Monad (SigEffect sig))
             => Proxy dom -> ECtx lang g
             -> LExp lang g s -> SigEffect sig (ValDom dom lang s)
evalToValDom proxy ρ e = fromJust . fromLVal proxy <$> eval' ρ e


