{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds
#-}

module DeepEmbedding where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe
import Debug.Trace
import GHC.TypeLits (Symbol(..))

import Prelim
import Types
import Classes
--import Proofs
import Tagless


----------------------------------------------------------------
-- Syntax ------------------------------------------------------
----------------------------------------------------------------

-- Linear expressions consist solely of variables, and constructors added from
-- different domains.
data LExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Var :: CSingletonCtx x τ γ => LExp lang γ τ
  Dom :: (Domain dom lang) --, Show (dom lang γ τ)) -- debugging
      => Proxy dom 
      -> dom lang γ τ
      -> LExp lang γ τ

dom :: forall dom lang γ σ. (Domain dom lang) --, Show (dom lang γ σ) )
    => dom lang γ σ -> LExp lang γ σ
dom e = Dom (Proxy @dom) e

-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom sig = Lang sig -> Exp sig
newtype Lang sig = Lang [Dom sig]





-- A well-formed domain is one in which the effect of the signature is a monad,
-- and the domain appears in the language
type WFDomain (dom :: Dom sig) (lang :: Lang sig) = 
    (CInLang dom lang, Monad (SigEffect sig))

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
class WFDomain dom lang => Domain (dom :: Dom sig) (lang :: Lang sig) where
  evalDomain  :: dom lang g σ
              -> CtxVal g
              -> SigEffect sig (LVal σ)

-----------------------------------------------------------
-- Evaluation ---------------------------------------------
-----------------------------------------------------------

instance Eval (LExp (lang :: Lang sig)) where
  eval :: forall γ τ. Monad (SigEffect sig)
       => LExp lang γ τ -> CtxVal γ -> SigEffect sig (LVal τ)
  eval Var                          γ = return $ singletonInv @_ @_ @τ @γ γ
  eval (Dom (Proxy :: Proxy dom) e) γ = evalDomain @_ @dom e γ

-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName

instance HasVar (LExp lang) where
  var = Var

data LolliExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Abs :: CAddCtx x σ γ γ'
      => VarName x σ -> Proxy '(γ,γ')
      -> LExp lang γ' τ
      -> LolliExp lang γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => Proxy '(γ1,γ2)
      -> LExp lang γ1 (σ ⊸ τ)
      -> LExp lang γ2 σ
      -> LolliExp lang γ τ

instance Domain LolliExp lang => HasLolli (LExp lang) where
  λ       :: forall x σ γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (LExp lang γ'' σ -> LExp lang γ' τ) -> LExp lang γ (σ ⊸ τ)
  λ f     = dom @LolliExp $ Abs (VarName @x) Proxy (f Var)
  e1 ^ e2 = dom @LolliExp $ App Proxy e1 e2

instance WFDomain LolliExp lang => Domain LolliExp (lang :: Lang sig) where
  evalDomain (Abs (VarName :: VarName x σ) (Proxy :: Proxy '(γ,γ')) e) γ = 
    return $ \s -> eval e (add @_ @x @σ @γ @γ' s γ)
  evalDomain (App (Proxy :: Proxy '(γ1,γ2)) f e) γ = do
      f' <- eval @sig f γ1
      x  <- eval @sig e γ2
      f' x
    where
      (γ1,γ2) = split @_ @γ1 @γ2 γ

------------------------------------------------------------------------

type family FromLang (lang :: Lang sig) :: [Dom sig] where
   FromLang ('Lang lang) = lang
type CInLang dom lang = CInList dom (FromLang lang)



{-
toDomain' :: forall dom lang σ.
             WFDomain dom lang
           => LVal lang σ -> Maybe (ValDom dom lang σ)
toDomain' (VDom (proxy :: Proxy dom') v) = -- cast @_ @(ValDom dom lang σ) v
  case compareInList (pfInList @_ @dom) (pfInList @_ @dom' @(FromLang lang)) of
--  case eqT @dom @dom' of
    Just Dict -> Just v
    Nothing   -> Nothing

toDomain :: forall dom lang σ.
          WFDomain dom lang
       => LVal lang σ -> ValDom dom lang σ
toDomain = fromJust . (toDomain' @dom)
-}
-- this function is partial if the value is not
-- in the specified domain
-- evalToValDom :: forall sig dom (lang :: Lang sig) g σ.
--                 (WFDomain dom lang, Monad (SigEffect sig), Typeable σ)
--              => Proxy dom -> ECtx lang g
--              -> LExp lang g σ -> SigEffect sig (ValDom dom lang σ)
-- evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

--instance Show (LExp lang γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e
