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
newtype Shallow γ τ = 
  SExp {runSExp :: ECtx Shallow γ -> Effect Shallow (LVal Shallow τ)}

instance Monad (Effect Shallow) => Eval Shallow where
  eval f γ = runSExp f γ
  fromVPut (VPut a) = return a

instance Monad (Effect Shallow) => HasVar Shallow where
  var (_ :: Proxy x) = SExp $ \γ -> return $ lookupSingleton @x γ

-----------------------------------------------------------
-----------------------------------------------------------

newtype instance LVal Shallow (MkLType ('LolliSig σ τ)) =
    VAbs (LVal Shallow σ -> Effect Shallow (LVal Shallow τ))

instance Monad (Effect Shallow) => HasLolli Shallow where
  λ f = SExp $ \(γ :: ECtx Shallow γ) -> return . VAbs $ \s -> 
         let x = (Proxy :: Proxy (Fresh γ)) 
         in runSExp (f $ var x) (addECtx x s γ)

  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => Shallow γ1 (σ ⊸ τ) -> Shallow γ2 σ -> Shallow γ τ
  f ^ s = SExp $ \γ -> do let (γ1,γ2) = splitECtx γ
                          VAbs f' <- runSExp f γ1
                          s'      <- runSExp s γ2
                          f' s'

newtype instance LVal Shallow (MkLType 'OneSig) = VUnit ()

instance Monad (Effect Shallow) => HasOne Shallow where
  unit = SExp $ \_ -> return $ VUnit ()
  letUnit (e1 :: Shallow γ1 One) (e2 :: Shallow γ2 τ) = SExp $ \γ -> do
    let (γ1,γ2) = splitECtx γ
    VUnit _ <- runSExp e1 γ1
    runSExp e2 γ2

newtype instance LVal Shallow (MkLType ('TensorSig σ1 σ2)) = 
    VPair (LVal Shallow σ1, LVal Shallow σ2)

instance Monad (Effect Shallow) => HasTensor Shallow where
  (e1 :: Shallow γ1 σ1) ⊗ (e2 :: Shallow γ2 σ2) = SExp $ \γ ->
    do let (γ1,γ2) = splitECtx γ
       v1 <- runSExp e1 γ1
       v2 <- runSExp e2 γ2
       return $ VPair (v1,v2)

  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22 
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => Shallow γ1 (σ1 ⊗ σ2)
      -> ((Shallow γ21 σ1, Shallow γ22 σ2) -> Shallow γ2'' τ)
      -> Shallow γ τ
  letPair e f = SExp $ \ρ -> do let (ρ1,ρ2) = splitECtx @γ1 @γ2 ρ
                                VPair (v1,v2) <- runSExp e ρ1
                                runSExp (f (var x1,var x2)) (add v1 v2 ρ2)
    where
      x1 = (Proxy :: Proxy x1)
      x2 = (Proxy :: Proxy x2)
      add v1 v2 ρ2 = addECtx x2 v2 (addECtx x1 v1 ρ2)


data instance LVal Shallow (MkLType 'BottomSig)

newtype instance LVal Shallow (MkLType ('PlusSig σ τ)) = 
    VPlus (Either (LVal Shallow σ) (LVal Shallow τ))
instance Monad (Effect Shallow) => HasPlus Shallow where
  inl e = SExp $ \γ -> VPlus . Left <$> runSExp e γ
  inr e = SExp $ \γ -> VPlus . Right <$> runSExp e γ
  caseof :: forall x σ1 σ2 τ γ γ1 γ2 γ21 γ21' γ22 γ22'.
            ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , CMerge γ1 γ2 γ, x ~ Fresh γ )
        => Shallow γ1 (σ1 ⊕ σ2)
        -> (Shallow γ21' σ1 -> Shallow γ21 τ)
        -> (Shallow γ22' σ2 -> Shallow γ22 τ)
        -> Shallow γ τ
  caseof e f1 f2 = SExp $ \γ ->
      let (γ1,γ2) = splitECtx @γ1 @γ2 γ
      in runSExp e γ1 >>= \case
        VPlus (Left s1)  -> runSExp (f1 $ var x) $ addECtx @σ1 x s1 γ2
        VPlus (Right s2) -> runSExp (f2 $ var x) $ addECtx @σ2 x s2 γ2
    where
      x = (Proxy :: Proxy x)

newtype instance LVal Shallow (MkLType ('WithSig σ τ)) = VWith (LVal Shallow σ, LVal Shallow τ)
instance Monad (Effect Shallow) => HasWith Shallow where
  e1 & e2 = SExp $ \γ -> 
    VWith <$> (liftM2 (,) (runSExp e1 γ) (runSExp e2 γ))
  proj1 e = SExp $ \γ -> do
    VWith (v1,_) <- runSExp e γ
    return v1
  proj2 e = SExp $ \γ -> do
    VWith (_,v2) <- runSExp e γ
    return v2

newtype instance LVal Shallow (MkLType ('LowerSig a)) = VPut a
instance Monad (Effect Shallow) => HasLower Shallow where
  put a = SExp $ \_ -> return $ VPut a
  (e :: Shallow γ1 (Lower a)) >! (f :: a -> Shallow γ2 τ) = SExp $ \ γ -> do
      (γ1,γ2) <- return $ splitECtx @γ1 @γ2 γ
      VPut a  <- runSExp e γ1
      runSExp (f a) γ2
