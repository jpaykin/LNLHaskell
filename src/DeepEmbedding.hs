{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds
#-}
{-# OPTIONS -fconstraint-solver-iterations=5 #-}

module DeepEmbedding where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe
import Debug.Trace
import GHC.TypeLits (Symbol(..))

import Prelim hiding (One)
import Types
import Classes
--import Proofs
import Tagless


----------------------------------------------------------------
-- Syntax ------------------------------------------------------
----------------------------------------------------------------

-- Linear expressions consist solely of variables, and constructors added from
-- different domains.
data LExp :: forall sig. Ctx sig -> LType sig -> * where
  Var :: CSingletonCtx x τ γ => LExp γ τ
  Dom :: forall sig (dom :: Dom sig) (γ :: Ctx sig) (τ :: LType sig).
         Domain dom --, Show (dom lang γ τ)) -- debugging
      => Proxy dom
      -> dom LExp γ τ
      -> LExp γ τ

dom :: forall dom γ σ. Domain dom => dom LExp γ σ -> LExp γ σ
dom = Dom (Proxy :: Proxy dom)
--dom :: forall dom lang γ σ. (Domain dom lang) --, Show (dom lang γ σ) )
--    => dom lang γ σ -> LExp lang γ σ
--dom e = Dom (Proxy @dom) e

-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom sig = Exp sig -> Exp sig
--newtype Lang sig = Lang [Dom sig]





-- A well-formed domain is one in which the effect of the signature is a monad,
-- and the domain appears in the language
--type WFDomain (dom :: Dom sig) (lang :: Lang sig) = 
--    (CInLang dom lang, Monad (SigEffect sig))

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
--class WFDomain dom lang => Domain (dom :: Dom sig) (lang :: Lang sig) where
class Domain (dom :: Dom sig) where
  evalDomain  :: Monad (SigEffect sig)
              => dom LExp g σ
              -> CtxVal g
              -> SigEffect sig (LVal σ)

-----------------------------------------------------------
-- Evaluation ---------------------------------------------
-----------------------------------------------------------

instance Eval (LExp :: Exp sig) where
  eval :: forall (γ :: Ctx sig) τ. Monad (SigEffect sig)
       => LExp γ τ -> CtxVal γ -> SigEffect sig (LVal τ)
  eval Var                          γ = return $ singletonInv @_ @_ @τ @γ γ
  eval (Dom (Proxy :: Proxy dom) e) γ = evalDomain e γ

-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName

instance HasVar LExp where
  var = Var

-- Lolli -------------------------------------------------

data LolliExp :: forall sig. Exp sig -> Exp sig where
  Abs :: CAddCtx x σ γ γ'
      => VarName x σ
      -> exp γ' τ
      -> LolliExp exp γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ)
      -> exp γ2 σ
      -> LolliExp exp γ τ

instance HasLolli LExp where
  λ       :: forall x sig (σ :: LType sig) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (LExp γ'' σ -> LExp γ' τ) -> LExp γ (σ ⊸ τ)
  λ f     = dom @LolliExp $ Abs (VarName @x) (f Var)
  e1 ^ e2 = dom @LolliExp $ App e1 e2

instance Domain LolliExp where
  evalDomain (Abs (VarName :: VarName x σ) (e :: LExp γ' τ)) γ = 
    return $ \s -> eval e (add @_ @x @σ @_ @γ' s γ)
  evalDomain (App (f :: LExp γ1 (σ ⊸ τ)) (e :: LExp γ2 σ)) γ = do
      f' <- eval f γ1
      x  <- eval e γ2
      f' x
    where
      (γ1,γ2) = split @_ @γ1 @γ2 γ

-- One -------------------------------------------------

data OneExp :: forall sig. Exp sig -> Exp sig where
  Unit :: OneExp exp 'Empty One
  LetUnit :: CMerge γ1 γ2 γ => exp γ1 One -> exp γ2 τ -> OneExp exp γ τ

instance HasOne LExp where
  unit = dom @OneExp Unit
  letUnit e1 e2 = dom @OneExp $ LetUnit e1 e2

instance Domain OneExp where
  evalDomain Unit () = return ()
  evalDomain (LetUnit (e1 :: LExp γ1 One) (e2 :: LExp γ2 τ)) ρ = do
      () <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = split @_ @γ1 @γ2 ρ

-- Tensor -------------------------------------------------

data TensorExp :: forall sig. Exp sig -> Exp sig where
  Pair :: CMerge γ1 γ2 γ
       => exp γ1 τ1 -> exp γ2 τ2 -> TensorExp exp γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2', CAddCtx x2 σ2 γ2' γ2'' )
          => VarName x1 σ1 -> VarName x2 σ2 -> Proxy γ2'
          -> exp γ1 (σ1 ⊗ σ2)
          -> exp γ2'' τ
          -> TensorExp exp γ τ

{-
instance HasTensor LExp where
  e1 ⊗ e2 = dom @TensorExp $ Pair e1 e2

  letPair :: forall x1 x2 sig (σ1 :: LType sig) σ2 τ γ1 γ2 γ γ2' γ2'' γ21 γ22.
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ )
      => LExp γ1 (σ1 ⊗ σ2)
      -> ((LExp γ21 σ1, LExp γ22 σ2) -> LExp γ2'' τ)
      -> LExp γ τ
  letPair e f = dom @TensorExp $ 
                LetPair (VarName @x1) (VarName @x2) (Proxy :: Proxy γ2') e e'
    where
      e' :: LExp γ2 τ
      e' = f (var @_ @_ @x1 @σ1 @γ21 ,var @_ @_ @x2 @σ2 @γ22)
-}
instance Domain TensorExp


-- Bottom -------------------------------------------------

-- Plus -------------------------------------------------

-- With -------------------------------------------------

-- Lower -------------------------------------------------

------------------------------------------------------------------------

--type family FromLang (lang :: Lang sig) :: [Dom sig] where
--   FromLang ('Lang lang) = lang
--type CInLang dom lang = CInList dom (FromLang lang)



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
