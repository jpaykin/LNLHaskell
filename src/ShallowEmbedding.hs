{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             LambdaCase
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors #-}

module ShallowEmbedding where

import Control.Monad (liftM2)


--import Prelim hiding (One)
import Types
import Classes
import Tagless


-- Shallow Embedding

data LExp m :: Exp where
  Exp :: forall m (γ :: Ctx) (τ :: LType).
         (SCtx m γ -> m (LVal m τ)) -> LExp m γ τ

instance Monad m => Eval m (LExp m) where
  eval (Exp f) γ = f γ

instance Monad m => HasVar (LExp m) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp m γ σ
  var = Exp $ \g -> return $ singletonInv @_ @_ @γ @m g

instance Monad m => HasLolli (LExp m) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp m γ'' σ -> LExp m γ' τ) -> LExp m γ (σ ⊸ τ)  
  λ f = Exp $ \(γ :: SCtx m γ) -> return . VAbs $ \s -> 
         let Exp g = f var
         in g (add @x @σ @γ @γ' s γ)
  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp m γ1 (σ ⊸ τ) -> LExp m γ2 σ -> LExp m γ τ
  Exp f ^ Exp s = Exp $ \g -> do
    (g1,g2) <- return $ split @γ1 @γ2 @_ @m g
    VAbs f' <- f g1
    s'      <- s g2
    f' s'

instance Monad m => HasOne (LExp m) where
  unit = Exp $ \_ -> return $ VUnit @m
  letUnit (Exp e1 :: LExp m γ1 One) (Exp e2 :: LExp m γ2 τ) = Exp $ \g -> do
    (g1,g2) <- return $ split @γ1 @γ2 @_ @m g
    VUnit   <- e1 g1
    e2 g2


instance Monad m => HasTensor (LExp m) where
  (Exp e1 :: LExp m γ1 σ1) ⊗ (Exp e2 :: LExp m γ2 σ2) = Exp $ \g ->
    let (g1,g2) = split @γ1 @γ2 @_ @m g
    in liftM2 VPair (e1 g1) (e2 g2)

  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ)
      => LExp m γ1 (σ1 ⊗ σ2)
      -> ((LExp m γ21 σ1, LExp m γ22 σ2) -> LExp m γ2'' τ)
      -> LExp m γ τ
  letPair (Exp e) f = Exp $ \ρ -> 
    let (ρ1,ρ2) = split @γ1 @(Remove x1 (Remove x2 γ2'')) ρ
        Exp e'  = f (var,var)
    in do
        VPair v1 v2 <- e ρ1
        e' (add @x2 @σ2 v2 (add @x1 @σ1 v1 ρ2))


instance Monad m => HasPlus (LExp m) where
  inl (Exp e) = Exp $ \g -> VLeft <$> e g
  inr (Exp e) = Exp $ \g -> VRight <$> e g
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => LExp m γ1 (σ1 ⊕ σ2)
        -> (LExp m γ21' σ1 -> LExp m γ21 τ)
        -> (LExp m γ22' σ2 -> LExp m γ22 τ)
        -> LExp m γ τ
  caseof (Exp e) f1 f2 = Exp $ \g ->
      let (g1,g2) = split @γ1 @γ2 @_ @m g
          Exp e1  = f1 var 
          Exp e2  = f2 var
      in e g1 >>= \case
        VLeft  s1 -> e1 $ add @x @σ1 @γ2 @γ21 s1 g2
        VRight s2 -> e2 $ add @x @σ2 @γ2 @γ22 s2 g2

instance Monad m => HasWith (LExp m) where
  Exp e1 & Exp e2 = Exp $ \g -> liftM2 VWith (e1 g) (e2 g)
  proj1 (Exp e)   = Exp $ \g -> do
    VWith v1 _ <- e g
    return v1
  proj2 (Exp e)   = Exp $ \g -> do
    VWith _ v2 <- e g
    return v2


instance Monad m => HasLower (LExp m) where
  put a = Exp $ \_ -> return $ VBang a
  (Exp e :: LExp m γ1 (Lower a)) >! (f :: a -> LExp m γ2 τ) = Exp $ \ g -> do
      (g1,g2) <- return $ split @γ1 @γ2 @_ @m g
      VBang a <- e g1
      Exp h   <- return $ f a
      h g2
