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


type Deep m = 'Sig m DExp


-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom = Exp -> Exp
data DExp (sig :: Sig) :: Ctx -> LType -> Type where
  Var :: CSingletonCtx x τ γ => DExp sig γ τ
  Dom :: forall sig (dom :: Dom) (γ :: Ctx) (τ :: LType).
         Domain sig dom 
      => Proxy dom
      -> dom (DExp sig) γ τ
      -> DExp sig γ τ

dom :: forall sig dom γ σ. Domain sig dom => dom (DExp sig) γ σ -> DExp sig γ σ
dom = Dom (Proxy :: Proxy dom)

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
class Monad (Effect sig) => Domain sig (dom :: Dom) where
  evalDomain  :: dom (LExp sig) g σ
              -> SCtx sig g
              -> Effect sig (LVal sig σ)

instance Monad m => Eval (Deep m) where
  eval :: forall (γ :: Ctx) τ. 
          LExp (Deep m) γ τ -> SCtx (Deep m) γ -> m (LVal (Deep m) τ)
  eval Var                          γ = undefined -- return γ
  eval (Dom (Proxy :: Proxy dom) e) γ = evalDomain e γ




-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName

instance HasVar (DExp m) where
  var :: forall x σ γ. CSingletonCtx x σ γ => DExp m γ σ
  var = Var

-- Lolli -------------------------------------------------

data LolliExp :: Exp -> Exp where
  Abs :: CAddCtx x σ γ γ'
      => VarName x σ
      -> exp γ' τ
      -> LolliExp exp γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ)
      -> exp γ2 σ
      -> LolliExp exp γ τ
data instance LVal (Deep m) (σ ⊸ τ) where
  VAbs :: CAddCtx x σ γ γ'
       => SCtx (Deep m) γ
       -> VarName x σ
       -> LExp (Deep m) γ' τ
       -> LVal (Deep m) (σ ⊸ τ)

instance Monad (Effect sig) => HasLolli (DExp sig) where
  λ       :: forall x (σ :: LType) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (DExp sig γ'' σ -> DExp sig γ' τ) -> DExp sig γ (σ ⊸ τ)
  λ f     = dom $ Abs (VarName @x) (f Var)
  e1 ^ e2 = dom $ App e1 e2

instance Monad (Effect sig) => Domain sig LolliExp where
{-
  evalDomain (Abs x e) γ = 
    return $ VAbs γ x e
  evalDomain (App (e1 :: DExp m γ1 (σ ⊸ τ)) (e2 :: DExp m γ2 σ)) ρ = do
    VAbs ρ' (x :: VarName x σ) e1' <- eval e1 ρ1
    v2 <- eval e2 ρ2
    eval e1' (add @x v2 ρ')
    where
      (γ1,γ2) = split γ
-}
{-


-- One -------------------------------------------------

data OneExp :: Exp -> Exp where
  Unit :: OneExp exp 'Empty One
  LetUnit :: CMerge γ1 γ2 γ => exp γ1 One -> exp γ2 τ -> OneExp exp γ τ
data instance LVal (Deep m) One where
  VUnit :: LVal (Deep m) One

instance Monad m => HasOne (DExp m) where
  unit = dom @m @OneExp Unit
  letUnit e1 e2 = dom @m @OneExp $ LetUnit e1 e2

instance Monad (Effect sig) => Domain sig OneExp where
{-
  evalDomain Unit _ = return VUnit
  evalDomain (LetUnit (e1 :: DExp m γ1 One) (e2 :: DExp m γ2 τ)) ρ = do
      VUnit <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = split @γ1 @γ2 @_ @m ρ
-}

-- Tensor -------------------------------------------------

data TensorExp :: forall. Exp -> Exp where
  Pair :: CMerge γ1 γ2 γ
       => exp γ1 τ1 -> exp γ2 τ2 -> TensorExp exp γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2'' )
          => VarName x1 σ1 -> VarName x2 σ2
          -> exp γ1 (σ1 ⊗ σ2)
          -> exp γ2'' τ
          -> TensorExp exp γ τ
data instance LVal (Deep m) (σ1 ⊗ σ2) = VPair (LVal (Deep m) σ1) (LVal (Deep m) σ2)


-- Bug is possibly a problem with 
-- instance sigs and ambiguous types?
-- https://ghc.haskell.org/trac/ghc/ticket/12587

instance Monad m => HasTensor (DExp m) where
  e1 ⊗ e2 = dom @m @TensorExp $ Pair e1 e2
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ)
      => DExp m γ1 (σ1 ⊗ σ2)
      -> ((Var (DExp m) x1 σ1, Var (DExp m) x2 σ2) -> DExp m γ2'' τ)
      -> DExp m γ τ
  letPair e f = dom @m @TensorExp $ 
                LetPair (VarName @x1 @σ1) (VarName @x2 @σ2) e $ f (x1,x2)
    where
      x1 :: Var (DExp m) x1 σ1
      x1 = Var
      x2 :: Var (DExp m) x2 σ2
      x2 = Var

instance Monad (Effect sig) => Domain sig TensorExp where
{-
  evalDomain (Pair (e1 :: DExp m γ1 τ1) (e2 :: DExp m γ2 τ2)) ρ =
      liftM2 VPair (eval e1 ρ1) (eval e2 ρ2)
    where
      (ρ1,ρ2) = split ρ
  evalDomain (LetPair (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                      (e :: DExp m γ1 (σ1 ⊗ σ2))
                      (e' :: DExp m γ2'' τ)) ρ = do
      VPair v1 v2 <- eval @m e ρ1
      eval e' (add @x2 @σ2 v2 
              (add @x1 @σ1 v1 ρ2))
    where
      (ρ1,ρ2) = split ρ
-}


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
--              -> DExp lang g σ ->Effect (ValDom dom lang σ)
-- evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

--instance Show (DExp lang γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e
-}
