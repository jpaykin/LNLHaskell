{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, AllowAmbiguousTypes, LambdaCase,
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
import Interface hiding (Pair, Inl, Inr, Put)


type Deep m = 'Sig m (DExp m) (DVal m)


-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom = Exp -> Exp
data DExp m :: Ctx -> LType -> Type where
  Var :: CSingletonCtx x τ γ => DExp m γ τ
  Dom :: forall (dom :: Dom) m (γ :: Ctx) (τ :: LType).
         Domain (Deep m) dom 
      => Proxy dom
      -> dom (DExp m) γ τ
      -> DExp m γ τ
data family DVal (m :: Type -> Type) (τ :: LType)

dom :: forall (dom :: Dom) m (γ :: Ctx) (τ :: LType).
         Domain (Deep m) dom 
      => dom (DExp m) γ τ
      -> DExp m γ τ
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
  eval Var                          γ = return $ singletonInv γ
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
data instance DVal m (σ ⊸ τ) where
  VAbs :: CAddCtx x σ γ γ'
       => SCtx (Deep m) γ
       -> VarName x σ
       -> DExp m γ' τ
       -> DVal m (σ ⊸ τ)

instance Monad m => HasLolli (DExp m) where
  λ       :: forall x (σ :: LType) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (DExp m γ'' σ -> DExp m γ' τ) -> DExp m γ (σ ⊸ τ)
  λ f     = dom $ Abs (VarName @x) (f Var)
  e1 ^ e2 = dom $ App e1 e2

instance Monad m => Domain (Deep m) LolliExp where
  evalDomain (Abs x e) γ = return $ VAbs γ x e
  evalDomain (App (e1 :: DExp m γ1 (σ ⊸ τ)) (e2 :: DExp m γ2 σ)) ρ = do
    VAbs ρ' (x :: VarName x σ) e1' <- eval e1 ρ1
    v2 <- eval e2 ρ2
    eval e1' (add @x v2 ρ')
    where
      (ρ1,ρ2) = split @γ1 @γ2 ρ



-- One -------------------------------------------------

data OneExp :: Exp -> Exp where
  Unit :: OneExp exp 'Empty One
  LetUnit :: CMerge γ1 γ2 γ => exp γ1 One -> exp γ2 τ -> OneExp exp γ τ
data instance DVal m One = VUnit

instance Monad m => HasOne (DExp m) where
  unit = dom Unit
  letUnit e1 e2 = dom $ LetUnit e1 e2

instance Monad m => Domain (Deep m) OneExp where
  evalDomain Unit _ = return VUnit
  evalDomain (LetUnit (e1 :: DExp m γ1 One) (e2 :: DExp m γ2 τ)) ρ = do
      VUnit <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = split @γ1 @γ2 ρ


-- Tensor -------------------------------------------------

data TensorExp :: Exp -> Exp where
  Pair :: CMerge γ1 γ2 γ
       => exp γ1 τ1 -> exp γ2 τ2 -> TensorExp exp γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2'' )
          => VarName x1 σ1 -> VarName x2 σ2
          -> exp γ1 (σ1 ⊗ σ2)
          -> exp γ2'' τ
          -> TensorExp exp γ τ
data instance DVal m (σ1 ⊗ σ2) = VPair (DVal m σ1) (DVal m σ2)


instance Monad m => HasTensor (DExp m) where
  e1 ⊗ e2 = dom $ Pair e1 e2
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => DExp m γ1 (σ1 ⊗ σ2)
      -> ((Var (DExp m) x1 σ1, Var (DExp m) x2 σ2) -> DExp m γ2'' τ)
      -> DExp m γ τ
  letPair e f = dom $ LetPair (VarName @x1 @σ1) (VarName @x2 @σ2) e $ f (x1,x2)
    where
      x1 :: Var (DExp m) x1 σ1
      x1 = Var
      x2 :: Var (DExp m) x2 σ2
      x2 = Var

instance Monad m => Domain (Deep m) TensorExp where
  evalDomain (Pair (e1 :: DExp m γ1 τ1) (e2 :: DExp m γ2 τ2)) ρ =
      liftM2 VPair (eval e1 ρ1) (eval e2 ρ2)
    where
      (ρ1,ρ2) = split ρ
  evalDomain (LetPair (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                      (e  :: DExp m γ1 (σ1 ⊗ σ2))
                      e' :: TensorExp (DExp m) γ τ) ρ = do
      VPair v1 v2 <- eval e ρ1
      eval e' (add @x2 @σ2 v2 (add @x1 @σ1 v1 ρ2))
    where
      (ρ1,ρ2) = split @γ1 @(Div γ γ1) ρ



-- Bottom -------------------------------------------------

-- Plus -------------------------------------------------

data PlusExp :: Exp -> Exp where
  Inl :: exp γ σ1 -> PlusExp exp γ (σ1 ⊕ σ2)
  Inr :: exp γ σ2 -> PlusExp exp γ (σ1 ⊕ σ2)
  Case :: (CMerge γ1 γ2 γ, CAddCtx x1 σ1 γ2 γ21, CAddCtx x2 σ2 γ2 γ22)
       => VarName x1 σ1 -> VarName x2 σ2
       -> exp γ1 (σ1 ⊕ σ2) -> exp γ21 τ -> exp γ22 τ -> PlusExp exp γ τ
data instance DVal m (σ1 ⊕ σ2) = VInl (DVal m σ1) | VInr (DVal m σ2)

instance Monad m => HasPlus (DExp m) where
  inl = dom . Inl
  inr = dom . Inr

  caseof :: forall x σ1 σ2 γ1 γ2 γ γ21 γ22 γ21' γ22' τ.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => DExp m γ1 (σ1 ⊕ σ2)
        -> (DExp m γ21' σ1 -> DExp m γ21 τ)
        -> (DExp m γ22' σ2 -> DExp m γ22 τ)
        -> DExp m γ τ
  caseof e f1 f2 = dom $ Case (VarName @x) (VarName @x) e (f1 var) (f2 var)

instance Monad m => Domain (Deep m) PlusExp where
  evalDomain (Inl e) ρ = VInl <$> eval e ρ
  evalDomain (Inr e) ρ = VInr <$> eval e ρ
  evalDomain (Case (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                   (e :: DExp m γ1 (σ1 ⊕ σ2)) e1 e2 :: PlusExp (DExp m) γ τ) ρ = 
      eval e ρ1 >>= \case 
        VInl v1 -> eval e1 (add @x1 v1 ρ2)
        VInr v2 -> eval e2 (add @x2 v2 ρ2)
    where
      (ρ1,ρ2) = split @γ1 @(Div γ γ1) ρ


-- With -------------------------------------------------

data WithExp :: Exp -> Exp where
  With :: exp γ τ1 -> exp γ τ2 -> WithExp exp γ (τ1 & τ2)
  Proj1 :: exp γ (τ1 & τ2) -> WithExp exp γ τ1
  Proj2 :: exp γ (τ1 & τ2) -> WithExp exp γ τ2
data instance DVal m (σ1 & σ2) where
  VWith :: SCtx (Deep m) γ -> DExp m γ σ1 -> DExp m γ σ2 -> DVal m (σ1 & σ2)

instance Monad m => HasWith (DExp m) where
  e1 & e2 = dom $ With e1 e2
  proj1 = dom . Proj1
  proj2 = dom . Proj2

instance Monad m => Domain (Deep m) WithExp where
  evalDomain (With e1 e2) ρ = return $ VWith ρ e1 e2
  evalDomain (Proj1 e) ρ = do
    VWith ρ' e1 _ <- eval e ρ
    eval e1 ρ'
  evalDomain (Proj2 e) ρ = do
    VWith ρ' _ e2 <- eval e ρ
    eval e2 ρ'

-- Lower -------------------------------------------------

data LowerExp :: Exp -> Exp where
  Put :: a -> LowerExp exp Empty (Lower a)
  LetBang :: CMerge γ1 γ2 γ
          => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> LowerExp exp γ τ
data instance DVal m (Lower a) = VPut a

instance Monad m => HasLower (DExp m) where
  put = dom . Put
  e >! f = dom $ LetBang e f

instance Monad m => Domain (Deep m) LowerExp where
  evalDomain (Put a) _ = return $ VPut a
  evalDomain (LetBang (e1 :: DExp m γ1 (Lower a)) (e2 :: a -> DExp m γ2 τ)) ρ = do
      VPut a <- eval e1 ρ1
      eval (e2 a) ρ2
    where
      (ρ1,ρ2) = split @γ1 @γ2 ρ

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
--              -> DExp g σ ->Effect (ValDom dom lang σ)
-- evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

--instance Show (DExp γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e

