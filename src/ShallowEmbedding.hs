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
import Interface


-- Shallow Embedding
data Shallow

data instance LExp Shallow γ τ where
  SExp :: forall (γ :: Ctx) (τ :: LType).
          (SCtx Shallow γ -> Effect Shallow (LVal Shallow τ)) 
       -> LExp Shallow γ τ



instance Monad (Effect Shallow) => Eval Shallow where
  eval (SExp f) γ = f γ
  fromVPut (VPut a) = return a



instance Monad (Effect Shallow) => HasVar Shallow where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp Shallow γ σ
  var = SExp $ \g -> return $ singletonInv g

-----------------------------------------------------------
-----------------------------------------------------------

data instance LVal Shallow (MkLType ('LolliSig σ τ)) =
    VAbs (LVal Shallow σ -> Effect Shallow (LVal Shallow τ))

instance Monad (Effect Shallow) => HasLolli Shallow where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'')
    => (LExp Shallow γ'' σ -> LExp Shallow γ' τ) -> LExp Shallow γ (σ ⊸ τ)  
  λ f = SExp $ \(γ :: SCtx Shallow γ) -> return . VAbs $ \s -> 
         let SExp g = f var
         in g (add @x s γ)
  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp Shallow γ1 (σ ⊸ τ) -> LExp Shallow γ2 σ -> LExp Shallow γ τ
  SExp f ^ SExp s = SExp $ \g -> do
    (g1,g2) <- return $ split g
    VAbs f' <- f g1
    s'      <- s g2
    f' s'

data instance LVal Shallow (MkLType 'OneSig) = VUnit
instance Monad (Effect Shallow) => HasOne Shallow where
  unit = SExp $ \_ -> return $ VUnit
  letUnit (SExp e1 :: LExp Shallow γ1 One) (SExp e2 :: LExp Shallow γ2 τ) = SExp $ \g -> do
    (g1,g2) <- return $ split g
    VUnit   <- e1 g1
    e2 g2

data instance LVal Shallow (MkLType ('TensorSig σ1 σ2)) = VPair (LVal Shallow σ1) (LVal Shallow σ2)

instance Monad (Effect Shallow) => HasTensor Shallow where
  (SExp e1 :: LExp Shallow γ1 σ1) ⊗ (SExp e2 :: LExp Shallow γ2 σ2) = SExp $ \g ->
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
      => LExp Shallow γ1 (σ1 ⊗ σ2)
      -> ((LExp Shallow γ21 σ1, LExp Shallow γ22 σ2) -> LExp Shallow γ2'' τ)
      -> LExp Shallow γ τ
  letPair (SExp e) f = SExp $ \ρ -> 
    let (ρ1,ρ2) = split ρ
        SExp e'  = f (var,var)
    in do
        VPair v1 v2 <- e ρ1
        e' (add @x2 @σ2 v2 (add @x1 @σ1 v1 ρ2))


data instance LVal Shallow (MkLType 'BottomSig)

data instance LVal Shallow (MkLType ('PlusSig σ τ)) = VLeft (LVal Shallow σ) | VRight (LVal Shallow τ)
instance Monad (Effect Shallow) => HasPlus Shallow where
  inl (SExp e) = SExp $ \g -> VLeft <$> e g
  inr (SExp e) = SExp $ \g -> VRight <$> e g
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , CMerge γ1 γ2 γ )
        => LExp Shallow γ1 (σ1 ⊕ σ2)
        -> (LExp Shallow γ21' σ1 -> LExp Shallow γ21 τ)
        -> (LExp Shallow γ22' σ2 -> LExp Shallow γ22 τ)
        -> LExp Shallow γ τ
  caseof (SExp e) f1 f2 = SExp $ \g ->
      let (g1,g2) = split g
          SExp e1  = f1 var 
          SExp e2  = f2 var
      in e g1 >>= \case
        VLeft  s1 -> e1 $ add @x @σ1 s1 g2
        VRight s2 -> e2 $ add @x @σ2 s2 g2

data instance LVal Shallow (MkLType ('WithSig σ τ)) = VWith (LVal Shallow σ) (LVal Shallow τ)
instance Monad (Effect Shallow) => HasWith Shallow where
  SExp e1 & SExp e2 = SExp $ \g -> liftM2 VWith (e1 g) (e2 g)
  proj1 (SExp e)   = SExp $ \g -> do
    VWith v1 _ <- e g
    return v1
  proj2 (SExp e)   = SExp $ \g -> do
    VWith _ v2 <- e g
    return v2

data instance LVal Shallow (MkLType ('LowerSig a)) = VPut a
instance Monad (Effect Shallow) => HasLower Shallow where
  put a = SExp $ \_ -> return $ VPut a
  (SExp e :: LExp Shallow γ1 (Lower a)) >! (f :: a -> LExp Shallow γ2 τ) = SExp $ \ g -> do
      (g1,g2) <- return $ split g
      VPut a <- e g1
      SExp h   <- return $ f a
      h g2
