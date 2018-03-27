{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             LambdaCase
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors 
                               -fno-warn-redundant-constraints #-}

module ShallowEmbedding where

import Control.Monad (liftM2)
import Data.Singletons

--import Prelim hiding (One)
import Types
import Classes
import Interface


-- Shallow Embedding
data Shallow

data instance LExp Shallow γ τ = 
  SExp {runSExp :: ECtx Shallow γ -> Effect Shallow (LVal Shallow τ)}
--  SExp :: forall (γ :: Ctx) (τ :: LType).
--          (SCtx Shallow γ -> Effect Shallow (LVal Shallow τ)) 
--       -> LExp Shallow γ τ

instance Monad (Effect Shallow) => Eval Shallow where
  eval f γ = runSExp f γ
  fromVPut (VPut a) = return a

instance Monad (Effect Shallow) => HasVar (LExp Shallow) where
  var x = SExp $ \g -> return $ Classes.lookup x g

-----------------------------------------------------------
-----------------------------------------------------------

data instance LVal Shallow (MkLType ('LolliSig σ τ)) =
    VAbs (LVal Shallow σ -> Effect Shallow (LVal Shallow τ))

instance Monad (Effect Shallow) => HasLolli (LExp Shallow) where
  λ f = SExp $ \(γ :: ECtx Shallow γ) -> return . VAbs $ \s -> 
         let x = (Proxy :: Proxy (Fresh γ)) 
         in runSExp (f $ var x) (add x s γ)

  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp Shallow γ1 (σ ⊸ τ) -> LExp Shallow γ2 σ -> LExp Shallow γ τ
  f ^ s = SExp $ \g -> do let (g1,g2) = split g
                          VAbs f' <- runSExp f g1
                          s'      <- runSExp s g2
                          f' s'

data instance LVal Shallow (MkLType 'OneSig) = VUnit
instance Monad (Effect Shallow) => HasOne (LExp Shallow) where
  unit = SExp $ \_ -> return $ VUnit
  letUnit (e1 :: LExp Shallow γ1 One) (e2 :: LExp Shallow γ2 τ) = SExp $ \g -> do
    let (g1,g2) = split g
    VUnit   <- runSExp e1 g1
    runSExp e2 g2

data instance LVal Shallow (MkLType ('TensorSig σ1 σ2)) = VPair (LVal Shallow σ1) (LVal Shallow σ2)

instance Monad (Effect Shallow) => HasTensor (LExp Shallow) where
  (e1 :: LExp Shallow γ1 σ1) ⊗ (e2 :: LExp Shallow γ2 σ2) = SExp $ \g ->
    let (g1,g2) = split g
    in liftM2 VPair (runSExp e1 g1) (runSExp e2 g2)

  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22 
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => LExp Shallow γ1 (σ1 ⊗ σ2)
      -> ((LExp Shallow γ21 σ1, LExp Shallow γ22 σ2) -> LExp Shallow γ2'' τ)
      -> LExp Shallow γ τ
  letPair e f = SExp $ \ρ -> do let (ρ1,ρ2) = split ρ
                                VPair v1 v2 <- runSExp e ρ1
                                runSExp (f (var x1,var x2)) (add x2 v2 (add x1 v1 ρ2))
    where
      x1 = (Proxy :: Proxy x1)
      x2 = (Proxy :: Proxy x2)


data instance LVal Shallow (MkLType 'BottomSig)

data instance LVal Shallow (MkLType ('PlusSig σ τ)) = VLeft (LVal Shallow σ) | VRight (LVal Shallow τ)
instance Monad (Effect Shallow) => HasPlus (LExp Shallow) where
  inl e = SExp $ \g -> VLeft <$> runSExp e g
  inr e = SExp $ \g -> VRight <$> runSExp e g
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , CMerge γ1 γ2 γ, x ~ Fresh γ )
        => LExp Shallow γ1 (σ1 ⊕ σ2)
        -> (LExp Shallow γ21' σ1 -> LExp Shallow γ21 τ)
        -> (LExp Shallow γ22' σ2 -> LExp Shallow γ22 τ)
        -> LExp Shallow γ τ
  caseof e f1 f2 = SExp $ \g ->
      let (g1,g2) = split g
      in runSExp e g1 >>= \case
        VLeft  s1 -> runSExp (f1 $ var x) $ add @σ1 x s1 g2
        VRight s2 -> runSExp (f2 $ var x) $ add @σ2 x s2 g2
    where
      x = (Proxy :: Proxy x)

data instance LVal Shallow (MkLType ('WithSig σ τ)) = VWith (LVal Shallow σ) (LVal Shallow τ)
instance Monad (Effect Shallow) => HasWith (LExp Shallow) where
  e1 & e2 = SExp $ \g -> liftM2 VWith (runSExp e1 g) (runSExp e2 g)
  proj1 e = SExp $ \g -> do
    VWith v1 _ <- runSExp e g
    return v1
  proj2 e = SExp $ \g -> do
    VWith _ v2 <- runSExp e g
    return v2

data instance LVal Shallow (MkLType ('LowerSig a)) = VPut a
instance Monad (Effect Shallow) => HasLower (LExp Shallow) where
  put a = SExp $ \_ -> return $ VPut a
  (e :: LExp Shallow γ1 (Lower a)) >! (f :: a -> LExp Shallow γ2 τ) = SExp $ \ g -> do
      (g1,g2) <- return $ split g
      VPut a  <- runSExp e g1
      runSExp (f a) g2
