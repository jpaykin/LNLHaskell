{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts
#-}

module LState where
 
import Data.Kind

import Types
import Classes
import Lang
import Subst
import Eval
import Interface

-- Signature
data LStateSig ty where
  LStateSig :: ty -> ty -> LStateSig ty
type LState s t = Sig ('LStateSig s t)

-- Domain specification

data LStateLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  LState :: exp g (s ⊸ s ⊗ t) -> LStateLExp exp g (LState s t)
  ApplyLState :: exp g (LState s t) -> LStateLExp exp g (s ⊸ s ⊗ t)

data LStateLVal (val :: LType sig -> *) :: LType sig -> * where
  VState :: val (s ⊸ s ⊗ t) -> LStateLVal val (LState s t)

type LStateDomain m = '(m, '(LStateLExp,LStateLVal))

lstate :: LExp (LStateDomain m) g (s ⊸ s ⊗ t) -> LExp (LStateDomain m) g (LState s t)
lstate e = Dom $ LState e

appLState :: CMerge g1 g2 g => LExp (LStateDomain m) g1 (LState s t)
          -> LExp (LStateDomain m) g2 s
          -> LExp (LStateDomain m) g (s ⊗ t)
appLState e1 e2 = Dom (ApplyLState e1) `app` e2

instance Monad m => Domain (LStateDomain m) where
  toExpDomain (VState v) = LState $ valToExp v

  substDomain pfA s (LState e) = lstate $ subst pfA s e
  substDomain pfA s (ApplyLState e) = Dom $ ApplyLState $ subst pfA s e

  evalDomain (LState e) = do
    v <- eval' e
    return . VDom $ VState v
  evalDomain (ApplyLState e) = do
    VDom (VState v) <- eval' e
    return v
