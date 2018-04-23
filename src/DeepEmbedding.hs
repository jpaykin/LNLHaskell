module DeepEmbedding where

import Prelude hiding (lookup)
--import Data.Kind
--import Data.Constraint
import Data.Proxy
--import Data.Maybe
--import Debug.Trace
--import GHC.TypeLits (Symbol(..))
import Control.Monad (liftM2)
--import Data.Singletons

-- import Prelim hiding (One)
import Types
import Classes
import Interface 

data Deep γ τ where
  Var :: CSingletonCtx x τ γ => Proxy x -> Deep γ τ
  Dom :: forall (dom :: Dom) (γ :: Ctx) (τ :: LType).
         Domain Deep dom 
      => dom Deep γ τ
      -> Deep γ τ

-- Expressions and values are indexed by languages, which are collections of
-- individual domains. This allows domains to be easily composed.
type Dom = Sig -> Sig

-- The domain type class characterizes well-formed domains in which
-- expressions in the domain evaluate to values in the langauge,
-- under the monad
class Domain exp (dom :: Dom) where
  evalDomain  :: Monad (Effect exp) 
              => dom exp g σ
              -> ECtx exp g
              -> Effect exp (LVal exp σ)

instance Eval Deep where
  eval :: forall (γ :: Ctx) τ. Monad (Effect Deep) =>
          Deep γ τ -> ECtx Deep γ -> Effect Deep (LVal Deep τ)
  eval (Var (_ :: Proxy x)) γ = return $ lookupSingleton @x γ
  eval (Dom e) γ = evalDomain e γ

  fromVPut (VPut a) = return a


-----------------------------------------------------------
-- Interface-----------------------------------------------
-----------------------------------------------------------

data VarName x σ = VarName (Proxy x)

instance HasVar Deep where
  var :: forall x σ γ. CSingletonCtx x σ γ => Proxy x -> Deep γ σ
  var = Var

-- Lolli -------------------------------------------------

data LolliExp :: Sig -> Sig where
  Abs :: CAddCtx x σ γ γ'
      => Proxy x
      -> exp γ' τ
      -> LolliExp exp γ (σ ⊸ τ)
  App :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ)
      -> exp γ2 σ
      -> LolliExp exp γ τ
data instance LVal Deep (σ ⊸ τ) where
  VAbs :: CAddCtx x σ γ γ'
       => ECtx Deep γ
       -> Proxy x
       -> Deep γ' τ
       -> LVal Deep (σ ⊸ τ)

instance HasLolli Deep where
  λ       :: forall x (σ :: LType) γ γ' γ'' τ.
             (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
          => (Deep γ'' σ -> Deep γ' τ) -> Deep γ (σ ⊸ τ)
  λ f     = Dom $ Abs x (f $ Var x) where x = (Proxy :: Proxy x)
  e1 ^ e2 = Dom $ App e1 e2

instance Domain Deep LolliExp where
  evalDomain (Abs x e) γ = return $ VAbs γ x e
  evalDomain (App (e1 :: Deep γ1 (σ ⊸ τ)) (e2 :: Deep γ2 σ)) ρ = do
    VAbs ρ' x e1' <- eval e1 ρ1
    v2 <- eval e2 ρ2
    eval e1' (addECtx x v2 ρ')
    where
      (ρ1,ρ2) = splitECtx @γ1 @γ2 ρ



-- One -------------------------------------------------

data OneExp :: Sig -> Sig where
  Unit :: OneExp exp '[] One
  LetUnit :: CMerge γ1 γ2 γ => exp γ1 One -> exp γ2 τ -> OneExp exp γ τ
data instance LVal Deep One = VUnit

instance HasOne Deep where
  unit = Dom Unit
  letUnit e1 e2 = Dom $ LetUnit e1 e2

instance Domain Deep OneExp where
  evalDomain Unit _ = return VUnit
  evalDomain (LetUnit (e1 :: Deep γ1 One) (e2 :: Deep γ2 τ)) ρ = do
      VUnit <- eval e1 ρ1
      eval e2 ρ2
    where
      (ρ1,ρ2) = splitECtx @γ1 @γ2 ρ


-- Tensor -------------------------------------------------

data TensorExp :: Sig -> Sig where
  Pair :: CMerge γ1 γ2 γ
       => exp γ1 τ1 -> exp γ2 τ2 -> TensorExp exp γ (τ1 ⊗ τ2)
  LetPair :: ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2'' )
--          => VarName x1 σ1 -> VarName x2 σ2
          => Proxy x1 -> Proxy x2
          -> exp γ1 (σ1 ⊗ σ2)
          -> exp γ2'' τ
          -> TensorExp exp γ τ
data instance LVal Deep (σ1 ⊗ σ2) = VPair (LVal Deep σ1) (LVal Deep σ2)


instance HasTensor Deep where
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
      => Deep γ1 (σ1 ⊗ σ2)
      -> ((Var Deep x1 σ1, Var Deep x2 σ2) -> Deep γ2'' τ)
      -> Deep γ τ
  letPair e f = Dom $ LetPair x1 x2 e $ f (Var x1,Var x2)
    where
      x1 :: Proxy x1
      x1 = Proxy
      x2 :: Proxy x2
      x2 = Proxy

instance  Domain Deep TensorExp where
  evalDomain (Pair (e1 :: Deep γ1 τ1) (e2 :: Deep γ2 τ2)) ρ =
      liftM2 VPair (eval e1 ρ1) (eval e2 ρ2)
    where
      (ρ1,ρ2) = splitECtx ρ
  evalDomain (LetPair x1 x2
                      (e  :: Deep γ1 (σ1 ⊗ σ2))
                      e' :: TensorExp Deep γ τ) ρ = do
      VPair v1 v2 <- eval e ρ1
      eval e' (addECtx x2 v2 (addECtx x1 v1 ρ2))
    where
      (ρ1,ρ2) = splitECtx @γ1 @(Div γ γ1) ρ



-- Bottom -------------------------------------------------

-- Plus -------------------------------------------------

data PlusExp :: Sig -> Sig where
  Inl :: exp γ σ1 -> PlusExp exp γ (σ1 ⊕ σ2)
  Inr :: exp γ σ2 -> PlusExp exp γ (σ1 ⊕ σ2)
  Case :: (CMerge γ1 γ2 γ, CAddCtx x1 σ1 γ2 γ21, CAddCtx x2 σ2 γ2 γ22)
       => Proxy x1 -> Proxy x2
       -> exp γ1 (σ1 ⊕ σ2) -> exp γ21 τ -> exp γ22 τ -> PlusExp exp γ τ
data instance LVal Deep (σ1 ⊕ σ2) = 
    VInl (LVal Deep σ1) | VInr (LVal Deep σ2)

instance  HasPlus Deep where
  inl = Dom . Inl
  inr = Dom . Inr

  caseof :: forall x σ1 σ2 γ1 γ2 γ γ21 γ22 γ21' γ22' τ.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => Deep γ1 (σ1 ⊕ σ2)
        -> (Deep γ21' σ1 -> Deep γ21 τ)
        -> (Deep γ22' σ2 -> Deep γ22 τ)
        -> Deep γ τ
  caseof e f1 f2 = Dom $ Case x x e (f1 $ var x) (f2 $ var x)
    where
      x = (Proxy :: Proxy x)

instance  Domain Deep PlusExp where
  evalDomain (Inl e) ρ = VInl <$> eval e ρ
  evalDomain (Inr e) ρ = VInr <$> eval e ρ
  evalDomain (Case x1 x2
                   (e :: Deep γ1 (σ1 ⊕ σ2)) e1 e2 :: PlusExp Deep γ τ) ρ = 
      eval e ρ1 >>= \case 
        VInl v1 -> eval e1 (addECtx x1 v1 ρ2)
        VInr v2 -> eval e2 (addECtx x2 v2 ρ2)
    where
      (ρ1,ρ2) = splitECtx @γ1 @(Div γ γ1) ρ


-- With -------------------------------------------------

data WithExp :: Sig -> Sig where
  With :: exp γ τ1 -> exp γ τ2 -> WithExp exp γ (τ1 & τ2)
  Proj1 :: exp γ (τ1 & τ2) -> WithExp exp γ τ1
  Proj2 :: exp γ (τ1 & τ2) -> WithExp exp γ τ2
data instance LVal Deep (σ1 & σ2) where
  VWith :: ECtx Deep γ -> Deep γ σ1 -> Deep γ σ2 
        -> LVal Deep (σ1 & σ2)

instance  HasWith Deep where
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

data LowerExp :: Sig -> Sig where
  Put :: a -> LowerExp exp '[] (Lower a)
  LetBang :: CMerge γ1 γ2 γ
          => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> LowerExp exp γ τ
data instance LVal Deep (Lower a) = VPut a

instance  HasLower Deep where
  put = Dom . Put
  e >! f = Dom $ LetBang e f

instance  Domain Deep LowerExp where
  evalDomain (Put a) _ = return $ VPut a
  evalDomain (LetBang (e1 :: Deep γ1 (Lower a)) (e2 :: a -> Deep γ2 τ)) ρ = do
      VPut a <- eval e1 ρ1
      eval (e2 a) ρ2
    where
      (ρ1,ρ2) = splitECtx @γ1 @γ2 ρ



-- Show instance
-- for debugging purposes

--instance Show (Deep γ t) where
--  show (Var pfS) = "x" ++ (show . inSNat $ singletonIn pfS)
--  show (Dom _ e) = show e

