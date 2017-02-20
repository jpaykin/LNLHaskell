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
import Data.Kind

--import Prelim hiding (One)
import Types
import Classes
import Interface


-- Shallow Embedding

type Shallow m = 'Sig m (SExp m) (SVal m)
data SExp (m :: Type -> Type) :: Exp where
  SExp :: forall m (γ :: Ctx) (τ :: LType).
          (SCtx (Shallow m) γ -> m (SVal m τ)) -> SExp m γ τ

data family SVal (m :: Type -> Type) (τ :: LType)


instance Monad m => Eval (Shallow m) where
  eval (SExp f) γ = f γ



instance Monad m => HasVar (SExp m) where
  var :: forall x σ γ. CSingletonCtx x σ γ => SExp m γ σ
  var = SExp $ \g -> return $ singletonInv g

-----------------------------------------------------------
-----------------------------------------------------------

data instance SVal m (MkLType ('LolliSig σ τ)) =
    VAbs (SVal m σ -> m (SVal m τ))

instance Monad m => HasLolli (SExp m) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'')
    => (SExp m γ'' σ -> SExp m γ' τ) -> SExp m γ (σ ⊸ τ)  
  λ f = SExp $ \(γ :: SCtx (Shallow m) γ) -> return . VAbs $ \s -> 
         let SExp g = f var
         in g (add @x s γ)
  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => SExp m γ1 (σ ⊸ τ) -> SExp m γ2 σ -> SExp m γ τ
  SExp f ^ SExp s = SExp $ \g -> do
    (g1,g2) <- return $ split g
    VAbs f' <- f g1
    s'      <- s g2
    f' s'

data instance SVal _ (MkLType 'OneSig) = VUnit
instance Monad m => HasOne (SExp m) where
  unit = SExp $ \_ -> return $ VUnit
  letUnit (SExp e1 :: SExp m γ1 One) (SExp e2 :: SExp m γ2 τ) = SExp $ \g -> do
    (g1,g2) <- return $ split g
    VUnit   <- e1 g1
    e2 g2

data instance SVal m (MkLType ('TensorSig σ1 σ2)) = VPair (SVal m σ1) (SVal m σ2)

instance Monad m => HasTensor (SExp m) where
  (SExp e1 :: SExp m γ1 σ1) ⊗ (SExp e2 :: SExp m γ2 σ2) = SExp $ \g ->
    let (g1,g2) = split g
    in liftM2 VPair (e1 g1) (e2 g2)

  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22)
      => SExp m γ1 (σ1 ⊗ σ2)
      -> ((SExp m γ21 σ1, SExp m γ22 σ2) -> SExp m γ2'' τ)
      -> SExp m γ τ
  letPair (SExp e) f = SExp $ \ρ -> 
    let (ρ1,ρ2) = split ρ
        SExp e'  = f (var,var)
    in do
        VPair v1 v2 <- e ρ1
        e' (add @x2 @σ2 v2 (add @x1 @σ1 v1 ρ2))


data instance SVal m (MkLType 'BottomSig)

data instance SVal m (MkLType ('PlusSig σ τ)) = VLeft (SVal m σ) | VRight (SVal m τ)
instance Monad m => HasPlus (SExp m) where
  inl (SExp e) = SExp $ \g -> VLeft <$> e g
  inr (SExp e) = SExp $ \g -> VRight <$> e g
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , CMerge γ1 γ2 γ )
        => SExp m γ1 (σ1 ⊕ σ2)
        -> (SExp m γ21' σ1 -> SExp m γ21 τ)
        -> (SExp m γ22' σ2 -> SExp m γ22 τ)
        -> SExp m γ τ
  caseof (SExp e) f1 f2 = SExp $ \g ->
      let (g1,g2) = split g
          SExp e1  = f1 var 
          SExp e2  = f2 var
      in e g1 >>= \case
        VLeft  s1 -> e1 $ add @x @σ1 s1 g2
        VRight s2 -> e2 $ add @x @σ2 s2 g2

data instance SVal m (MkLType ('WithSig σ τ)) = VWith (SVal m σ) (SVal m τ)
instance Monad m => HasWith (SExp m) where
  SExp e1 & SExp e2 = SExp $ \g -> liftM2 VWith (e1 g) (e2 g)
  proj1 (SExp e)   = SExp $ \g -> do
    VWith v1 _ <- e g
    return v1
  proj2 (SExp e)   = SExp $ \g -> do
    VWith _ v2 <- e g
    return v2

data instance SVal m (MkLType ('LowerSig a)) = VBang a
instance Monad m => HasLower (SExp m) where
  put a = SExp $ \_ -> return $ VBang a
  (SExp e :: SExp m γ1 (Lower a)) >! (f :: a -> SExp m γ2 τ) = SExp $ \ g -> do
      (g1,g2) <- return $ split g
      VBang a <- e g1
      SExp h   <- return $ f a
      h g2
