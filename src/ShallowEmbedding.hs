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

data LExp sig :: Exp sig where
  Exp :: forall (γ :: Ctx sig) (τ :: LType sig).
         (CtxVal γ -> SigEffect sig (LVal τ)) -> LExp sig γ τ

instance Eval (LExp sig) where
  eval (Exp f) γ = f γ

instance Monad (SigEffect sig) => HasVar (LExp sig) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp sig γ σ
  var = Exp $ \g -> return $ singletonInv @_ @_ @σ @γ g

instance Monad (SigEffect sig) => HasLolli (LExp sig) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp sig γ'' σ -> LExp sig γ' τ) -> LExp sig γ (σ ⊸ τ)  
  λ f = Exp $ \(γ :: CtxVal γ) -> return $ \s -> 
         let Exp g = f var
         in g (add @_ @x @σ @γ @γ' s γ)
  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp sig γ1 (σ ⊸ τ) -> LExp sig γ2 σ -> LExp sig γ τ
  Exp f ^ Exp s = Exp $ \g -> do
    (g1,g2) <- return $ split @_ @γ1 @γ2 g
    f' <- f g1
    s' <- s g2
    f' s'

instance Monad (SigEffect sig) => HasOne (LExp sig) where
  unit = Exp return
  letUnit (Exp e1 :: LExp sig γ1 One) (Exp e2 :: LExp sig γ2 τ) = Exp $ \g -> do
    (g1,g2) <- return $ split @_ @γ1 @γ2 g
    ()      <- e1 g1
    e2 g2


instance Monad (SigEffect sig) => HasTensor (LExp sig) where
  (Exp e1 :: LExp sig γ1 σ1) ⊗ (Exp e2 :: LExp sig γ2 σ2) = Exp $ \g ->
    let (g1,g2) = split @_ @γ1 @γ2 g
    in liftM2 (,) (e1 g1) (e2 g2)

  -- letPair :: forall x1 x2 (σ1 :: LType sig) σ2 τ γ1 γ2 γ γ2' γ2'' γ21 γ22.
  --            ( CMerge γ1 γ2 γ
  --            , CAddCtx x1 σ1 γ2 γ2'
  --            , CAddCtx x2 σ2 γ2' γ2''
  --            , CSingletonCtx x1 σ1 γ21
  --            , CSingletonCtx x2 σ2 γ22
  --            , x1 ~ Fresh γ, x2 ~ Fresh2 γ )
  --     => LExp sig γ1 (σ1 ⊗ σ2)
  --     -> ((LExp sig γ21 σ1, LExp sig γ22 σ2) -> LExp sig γ2'' τ)
  --     -> LExp sig γ τ
  letPair = undefined
--  letPair (Exp e) f = Exp $ \g -> 
--    let (g1,g2) = split @_ @γ1 @γ2 g
--        Exp e'  = f (var @_ @_ @σ1 @γ21, var @_ @_ @σ2 @γ22)
--        g2' s1  = (add @_ @x1 @σ1 @γ2 @γ2' s1 g2 :: CtxVal γ2')
--        g2'' s1 s2 = (add @_ @x2 @σ2 @γ2' @γ2'' s2 (g2' s1) :: CtxVal γ2'')
--    in do
--      (s1,s2) <- e g1
--      e' (g2'' s1 s2)

instance Monad (SigEffect sig) => HasPlus (LExp sig) where
  inl (Exp e) = Exp $ \g -> Left <$> e g
  inr (Exp e) = Exp $ \g -> Right <$> e g
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => LExp sig γ1 (σ1 ⊕ σ2)
        -> (LExp sig γ21' σ1 -> LExp sig γ21 τ)
        -> (LExp sig γ22' σ2 -> LExp sig γ22 τ)
        -> LExp sig γ τ
  caseof (Exp e) f1 f2 = Exp $ \g ->
      let (g1,g2) = split @_ @γ1 @γ2 g
          Exp e1  = f1 var 
          Exp e2  = f2 var
      in e g1 >>= \case
        Left  s1 -> e1 $ add @_ @x @σ1 @γ2 @γ21 s1 g2
        Right s2 -> e2 $ add @_ @x @σ2 @γ2 @γ22 s2 g2

instance Monad (SigEffect sig) => HasWith (LExp sig) where
  Exp e1 & Exp e2 = Exp $ \g -> liftM2 (,) (e1 g) (e2 g)
  proj1 (Exp e)   = Exp $ \g -> fst <$> e g
  proj2 (Exp e)   = Exp $ \g -> snd <$> e g


instance Monad (SigEffect sig) => HasLower (LExp sig) where
  put a = Exp $ \() -> return a
  (>!) :: forall γ1 γ2 γ a τ.
          CMerge γ1 γ2 γ
       => LExp sig γ1 (Lower a) -> (a -> LExp sig γ2 τ) -> LExp sig γ τ
  (Exp e) >! f = Exp $ \ g -> do
      (g1,g2) <- return $ split @_ @γ1 @γ2 g
      Exp h   <- f <$> e g1
      h g2
