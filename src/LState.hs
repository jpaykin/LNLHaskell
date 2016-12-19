{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module LState where
 
import Data.Kind
import Data.Proxy

import Types
import Classes
import Lang
import Subst
import Eval
import Interface
import Domain

-- Signature
data LStateSig ty where
  LStateSig :: ty -> ty -> LStateSig ty

class Monad (SigEffect sig) => HasLStateSig sig where
  type LState (s :: LType sig) (t :: LType sig) = (r :: LType sig) | r -> s t

instance Monad m => HasLStateSig '(m,LStateSig) where
  type LState s t = 'Sig ('LStateSig s t)

data LStateLVal (val :: LType sig -> *) :: LType sig -> * where
  VState :: forall sig (val :: LType sig -> *) s t.
            HasLStateSig sig 
         => val (s ⊸ s ⊗ t) -> LStateLVal val (LState s t)
type LStateDom sig = (LStateLVal :: Dom sig)


class HasLStateSig sig => HasLStateDom (dom :: Dom sig) where
  vstate :: LVal dom (s ⊸ s ⊗ t) -> LVal dom (LState s t)

instance HasLStateSig sig => HasLStateDom (LStateDom sig) where
  vstate v = VDom (Proxy :: Proxy LStateLExp) $ VState v


-- Domain specification

data LStateLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  LState :: exp g (s ⊸ s ⊗ t) -> LStateLExp exp g (LState s t)
  ApplyLState :: exp g (LState s t) -> LStateLExp exp g (s ⊸ s ⊗ t)


class HasLStateSig sig => HasLState (dom :: Dom sig) (exp :: ExpDom sig) where
  lstate :: LExp dom g (s ⊸ s ⊗ t) -> LExp dom g (LState s t)
  applyLState :: CMerge g1 g2 g
              => LExp dom g1 (LState s t)
              -> LExp dom g2 s
              -> LExp dom g (s ⊗ t)
instance HasLStateDom dom => HasLState dom LStateLExp where
  lstate e = Dom Proxy $ LState e
  applyLState e1 e2 = (Dom Proxy $ ApplyLState e1) `app` e2


instance HasLStateDom dom => Domain dom LStateLExp where
  substDomain _ pfA s (LState e) = Dom Proxy $ LState $ subst pfA s e
  evalDomain  _ (LState e) = fmap vstate $ eval' e
  evalDomain  _ (ApplyLState e) = undefined


instance HasLStateSig sig => ToExp (LStateDom sig) LStateLExp where
  valToExpDomain _ (VState v) = LState $ valToExp v


{-




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
-}
