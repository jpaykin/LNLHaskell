{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds
#-}
--{-# OPTIONS -fconstraint-solver-iterations=5 #-}

module DeepEmbedding where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe
import Debug.Trace
import GHC.TypeLits (Symbol(..))
import Control.Monad (liftM2)

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
data LExp (m :: Type -> Type) :: Ctx -> LType -> Type where
  Var :: CSingletonCtx x τ γ => LExp m γ τ
  Dom :: forall m (dom :: Dom) (γ :: Ctx) (τ :: LType).
         Domain m dom 
      => Proxy dom
      -> dom (LExp m) γ τ
      -> LExp m γ τ

dom :: forall m dom γ σ. Domain m dom => dom (LExp m) γ σ -> LExp m γ σ
dom = Dom (Proxy :: Proxy dom)

-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom = Exp -> Exp
--newtype Lang = Lang [Dom]





-- A well-formed domain is one in which the effect of thenature is a monad,
-- and the domain appears in the language
--type WFDomain (dom :: Dom) (lang :: Lang) = 
--    (CInLang dom lang, Monad (SigEffect))

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
--class WFDomain dom lang => Domain (dom :: Dom) (lang :: Lang) where
class Monad m => Domain m (dom :: Dom) where
  evalDomain  :: dom (LExp m) g σ
              -> CtxVal m g
              -> m (LVal m σ)

-----------------------------------------------------------
-- Evaluation ---------------------------------------------
-----------------------------------------------------------

instance Monad m => Eval m (LExp m) where
  eval :: forall (γ :: Ctx) τ. 
          LExp m γ τ -> CtxVal m γ -> m (LVal m τ)
  eval Var                          γ = undefined -- return γ
  eval (Dom (Proxy :: Proxy dom) e) γ = evalDomain e γ

-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName

instance HasVar (LExp m) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp m γ σ
  var = Var

-- Lolli -------------------------------------------------

data LolliExp :: forall. Exp -> Exp where
  Abs :: CAddCtx x σ γ γ'
      => VarName x σ
      -> exp γ' τ
      -> LolliExp exp γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ)
      -> exp γ2 σ
      -> LolliExp exp γ τ

instance Monad m => HasLolli (LExp m) where
  λ       :: forall x (σ :: LType) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (LExp m γ'' σ -> LExp m γ' τ) -> LExp m γ (σ ⊸ τ)
  λ f     = dom @m @LolliExp $ Abs (VarName @x) (f Var)
  e1 ^ e2 = dom @m @LolliExp $ App e1 e2

instance Monad m => Domain m LolliExp where
  evalDomain (Abs (VarName :: VarName x σ) (e :: LExp m γ' τ)) γ = 
    return . VAbs $ \s -> eval e (add @x @σ @_ @γ' @m s γ)
  evalDomain (App (f :: LExp m γ1 (σ ⊸ τ)) (e :: LExp m γ2 σ)) γ = do
      VAbs f' <- eval f γ1
      x  <- eval e γ2
      f' x
    where
      (γ1,γ2) = split @γ1 @γ2 @_ @m γ

-- One -------------------------------------------------

data OneExp :: Exp -> Exp where
  Unit :: OneExp exp 'Empty One
  LetUnit :: CMerge γ1 γ2 γ => exp γ1 One -> exp γ2 τ -> OneExp exp γ τ

instance Monad m => HasOne (LExp m) where
  unit = dom @m @OneExp Unit
  letUnit e1 e2 = dom @m @OneExp $ LetUnit e1 e2

instance Monad m => Domain m OneExp where
  evalDomain Unit () = return VUnit
  evalDomain (LetUnit (e1 :: LExp m γ1 One) (e2 :: LExp m γ2 τ)) ρ = do
      VUnit <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = split @γ1 @γ2 @_ @m ρ

-- Tensor -------------------------------------------------

data TensorExp :: forall. Exp -> Exp where
  Pair :: CMerge γ1 γ2 γ
       => exp γ1 τ1 -> exp γ2 τ2 -> TensorExp exp γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2', CAddCtx x2 σ2 γ2' γ2'' )
          => VarName x1 σ1 -> VarName x2 σ2 -> Proxy '(γ2,γ2')
          -> exp γ1 (σ1 ⊗ σ2)
          -> exp γ2'' τ
          -> TensorExp exp γ τ


-- Bug is possibly a problem with 
-- instance sigs and ambiguous types?
-- https://ghc.haskell.org/trac/ghc/ticket/12587

instance Monad m => HasTensor (LExp m) where
  e1 ⊗ e2 = dom @m @TensorExp $ Pair e1 e2

{-
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ )
      => LExp m γ1 (σ1 ⊗ σ2)
      -> ((LExp m γ21 σ1, LExp m γ22 σ2) -> LExp m γ2'' τ)
      -> LExp m γ τ
  letPair e f = Dom (Proxy :: Proxy TensorExp) $ 
                LetPair (VarName @x1) (VarName @x2) (Proxy :: Proxy '(γ2,γ2')) e 
                  $ f(x1,x2)
    where
      x1 :: LExp m γ21 σ1
      x1 = var @_ @x1
      x2 :: LExp m γ22 σ2
      x2 = var @_ @x2
-}

instance Monad m => Domain m TensorExp where
  evalDomain (Pair (e1 :: LExp m γ1 τ1) (e2 :: LExp m γ2 τ2)) ρ =
      liftM2 VPair (eval e1 ρ1) (eval e2 ρ2)
    where
      (ρ1,ρ2) = split @γ1 @γ2 @_ @m ρ
  evalDomain (LetPair (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                      (Proxy :: Proxy '(γ2,γ2'))
                      (e :: LExp m γ1 (σ1 ⊗ σ2))
                      (e' :: LExp m γ2'' τ)) ρ = do
      VPair v1 v2 <- eval @m e ρ1
      eval e' (add @x2 @σ2 @γ2' @γ2'' v2 (add @x1 @σ1 @γ2 @γ2' v1 ρ2))
    where
      (ρ1,ρ2) = split @γ1 @γ2 @_ @m ρ


-- Bottom -------------------------------------------------

-- Plus -------------------------------------------------

-- With -------------------------------------------------

-- Lower -------------------------------------------------

------------------------------------------------------------------------

--type family FromLang (lang :: Lang) :: [Dom] where
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
-- evalToValDom :: forall dom (lang :: Lang) g σ.
--                 (WFDomain dom lang, Monad (SigEffect), Typeable σ)
--              => Proxy dom -> ECtx lang g
--              -> LExp lang g σ ->Effect (ValDom dom lang σ)
-- evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

--instance Show (LExp lang γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e
