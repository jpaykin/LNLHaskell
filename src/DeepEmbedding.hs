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

data Deep

-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom = Sig -> Exp
data instance LExp Deep γ τ where
  Var :: CSingletonCtx x τ γ => LExp Deep γ τ
  Dom :: forall (dom :: Dom) m (γ :: Ctx) (τ :: LType).
         Domain Deep dom 
      => dom Deep γ τ
      -> LExp Deep γ τ


-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
class Domain sig (dom :: Dom) where
  evalDomain  :: Monad (Effect sig) 
              => dom sig g σ
              -> SCtx sig g
              -> Effect sig (LVal sig σ)

instance Eval Deep where
  eval :: forall (γ :: Ctx) τ. Monad (Effect Deep) =>
          LExp Deep γ τ -> SCtx Deep γ -> Effect Deep (LVal Deep τ)
  eval Var     γ = return $ singletonInv γ
  eval (Dom e) γ = evalDomain e γ

  fromVPut (VPut a) = return a




-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName

instance HasVar (LExp Deep) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp Deep γ σ
  var = Var

-- Lolli -------------------------------------------------

data LolliExp :: Sig -> Exp where
  Abs :: CAddCtx x σ γ γ'
      => VarName x σ
      -> LExp sig γ' τ
      -> LolliExp sig γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => LExp sig γ1 (σ ⊸ τ)
      -> LExp sig γ2 σ
      -> LolliExp sig γ τ
data instance LVal Deep (σ ⊸ τ) where
  VAbs :: CAddCtx x σ γ γ'
       => SCtx Deep γ
       -> VarName x σ
       -> LExp Deep γ' τ
       -> LVal Deep (σ ⊸ τ)

instance HasLolli (LExp Deep) where
  λ       :: forall x (σ :: LType) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (LExp Deep γ'' σ -> LExp Deep γ' τ) -> LExp Deep γ (σ ⊸ τ)
  λ f     = Dom $ Abs (VarName @x) (f Var)
  e1 ^ e2 = Dom $ App e1 e2

instance Domain Deep LolliExp where
  evalDomain (Abs x e) γ = return $ VAbs γ x e
  evalDomain (App (e1 :: LExp Deep γ1 (σ ⊸ τ)) (e2 :: LExp Deep γ2 σ)) ρ = do
    VAbs ρ' (x :: VarName x σ) e1' <- eval e1 ρ1
    v2 <- eval e2 ρ2
    eval e1' (add @x v2 ρ')
    where
      (ρ1,ρ2) = split @γ1 @γ2 ρ



-- One -------------------------------------------------

data OneExp :: Sig -> Exp where
  Unit :: OneExp sig 'Empty One
  LetUnit :: CMerge γ1 γ2 γ => LExp sig γ1 One -> LExp sig γ2 τ -> OneExp sig γ τ
data instance LVal Deep One = VUnit

instance HasOne (LExp Deep) where
  unit = Dom Unit
  letUnit e1 e2 = Dom $ LetUnit e1 e2

instance Domain Deep OneExp where
  evalDomain Unit _ = return VUnit
  evalDomain (LetUnit (e1 :: LExp Deep γ1 One) (e2 :: LExp Deep γ2 τ)) ρ = do
      VUnit <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = split @γ1 @γ2 ρ


-- Tensor -------------------------------------------------

data TensorExp :: Sig -> Exp where
  Pair :: CMerge γ1 γ2 γ
       => LExp sig γ1 τ1 -> LExp sig γ2 τ2 -> TensorExp sig γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2'' )
          => VarName x1 σ1 -> VarName x2 σ2
          -> LExp sig γ1 (σ1 ⊗ σ2)
          -> LExp sig γ2'' τ
          -> TensorExp sig γ τ
data instance LVal Deep (σ1 ⊗ σ2) = VPair (LVal Deep σ1) (LVal Deep σ2)


instance HasTensor (LExp Deep) where
  e1 ⊗ e2 = Dom $ Pair e1 e2
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => LExp Deep γ1 (σ1 ⊗ σ2)
      -> ((Var Deep x1 σ1, Var Deep x2 σ2) -> LExp Deep γ2'' τ)
      -> LExp Deep γ τ
  letPair e f = Dom $ LetPair (VarName @x1 @σ1) (VarName @x2 @σ2) e $ f (x1,x2)
    where
      x1 :: Var Deep x1 σ1
      x1 = Var
      x2 :: Var Deep x2 σ2
      x2 = Var

instance  Domain Deep TensorExp where
  evalDomain (Pair (e1 :: LExp Deep γ1 τ1) (e2 :: LExp Deep γ2 τ2)) ρ =
      liftM2 VPair (eval e1 ρ1) (eval e2 ρ2)
    where
      (ρ1,ρ2) = split ρ
  evalDomain (LetPair (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                      (e  :: LExp Deep γ1 (σ1 ⊗ σ2))
                      e' :: TensorExp Deep γ τ) ρ = do
      VPair v1 v2 <- eval e ρ1
      eval e' (add @x2 @σ2 v2 (add @x1 @σ1 v1 ρ2))
    where
      (ρ1,ρ2) = split @γ1 @(Div γ γ1) ρ



-- Bottom -------------------------------------------------

-- Plus -------------------------------------------------

data PlusExp :: Sig -> Exp where
  Inl :: LExp sig γ σ1 -> PlusExp sig γ (σ1 ⊕ σ2)
  Inr :: LExp sig γ σ2 -> PlusExp sig γ (σ1 ⊕ σ2)
  Case :: (CMerge γ1 γ2 γ, CAddCtx x1 σ1 γ2 γ21, CAddCtx x2 σ2 γ2 γ22)
       => VarName x1 σ1 -> VarName x2 σ2
       -> LExp sig γ1 (σ1 ⊕ σ2) -> LExp sig γ21 τ -> LExp sig γ22 τ -> PlusExp sig γ τ
data instance LVal Deep (σ1 ⊕ σ2) = 
    VInl (LVal Deep σ1) | VInr (LVal Deep σ2)

instance  HasPlus (LExp Deep) where
  inl = Dom . Inl
  inr = Dom . Inr

  caseof :: forall x σ1 σ2 γ1 γ2 γ γ21 γ22 γ21' γ22' τ.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => LExp Deep γ1 (σ1 ⊕ σ2)
        -> (LExp Deep γ21' σ1 -> LExp Deep γ21 τ)
        -> (LExp Deep γ22' σ2 -> LExp Deep γ22 τ)
        -> LExp Deep γ τ
  caseof e f1 f2 = Dom $ Case (VarName @x) (VarName @x) e (f1 var) (f2 var)

instance  Domain Deep PlusExp where
  evalDomain (Inl e) ρ = VInl <$> eval e ρ
  evalDomain (Inr e) ρ = VInr <$> eval e ρ
  evalDomain (Case (_ :: VarName x1 σ1) (_ :: VarName x2 σ2)
                   (e :: LExp Deep γ1 (σ1 ⊕ σ2)) e1 e2 :: PlusExp Deep γ τ) ρ = 
      eval e ρ1 >>= \case 
        VInl v1 -> eval e1 (add @x1 v1 ρ2)
        VInr v2 -> eval e2 (add @x2 v2 ρ2)
    where
      (ρ1,ρ2) = split @γ1 @(Div γ γ1) ρ


-- With -------------------------------------------------

data WithExp :: Sig -> Exp where
  With :: LExp sig γ τ1 -> LExp sig γ τ2 -> WithExp sig γ (τ1 & τ2)
  Proj1 :: LExp sig γ (τ1 & τ2) -> WithExp sig γ τ1
  Proj2 :: LExp sig γ (τ1 & τ2) -> WithExp sig γ τ2
data instance LVal Deep (σ1 & σ2) where
  VWith :: SCtx Deep γ -> LExp Deep γ σ1 -> LExp Deep γ σ2 
        -> LVal Deep (σ1 & σ2)

instance  HasWith (LExp Deep) where
  e1 & e2 = Dom $ With e1 e2
  proj1 = Dom . Proj1
  proj2 = Dom . Proj2

instance  Domain Deep WithExp where
  evalDomain (With e1 e2) ρ = return $ VWith ρ e1 e2
  evalDomain (Proj1 e) ρ = do
    VWith ρ' e1 _ <- eval e ρ
    eval e1 ρ'
  evalDomain (Proj2 e) ρ = do
    VWith ρ' _ e2 <- eval e ρ
    eval e2 ρ'

-- Lower -------------------------------------------------

data LowerExp :: Sig -> Exp where
  Put :: a -> LowerExp sig Empty (Lower a)
  LetBang :: CMerge γ1 γ2 γ
          => LExp sig γ1 (Lower a) -> (a -> LExp sig γ2 τ) -> LowerExp sig γ τ
data instance LVal Deep (Lower a) = VPut a

instance  HasLower (LExp Deep) where
  put = Dom . Put
  e >! f = Dom $ LetBang e f

instance  Domain Deep LowerExp where
  evalDomain (Put a) _ = return $ VPut a
  evalDomain (LetBang (e1 :: LExp Deep γ1 (Lower a)) (e2 :: a -> LExp Deep γ2 τ)) ρ = do
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
--              -> Deep g σ ->Effect (ValDom dom lang σ)
-- evalToValDom proxy ρ e = fromLVal proxy <$> eval' ρ e


---------


-- Show instance
-- for debugging purposes

--instance Show (Deep γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e

