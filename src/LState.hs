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
import Data.Constraint

import Types
import Classes
import Lang
import Subst
import Eval
import Interface

-- Signature
data LStateSig ty where
  LStateSig :: ty -> ty -> LStateSig ty
type LState (s :: LType sig) (t :: LType sig) 
    = 'Sig (InSig LStateSig sig) ('LStateSig s t)

class (Monad (SigEffect sig), CInSig LStateSig sig) => HasLStateSig sig
instance (Monad (SigEffect sig), CInSig LStateSig sig) => HasLStateSig sig


data LStateLVal (val :: LType sig -> *) :: LType sig -> * where
  VState :: forall sig (val :: LType sig -> *) s t.
            val (s ⊸ s ⊗ t) -> LStateLVal val (LState sig s t)

data LStateLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  LState :: exp g (s ⊸ s ⊗ t) -> LStateLExp exp g (LState sig s t)
  ApplyLState :: exp g (LState sig s t) -> LStateLExp exp g (s ⊸ s ⊗ t)

type LStateDom = '(LStateLExp, LStateLVal)
----------------------------------------------------------

class (Monad (SigEffect sig), CInList i '(LStateLExp, LStateLVal) (dom :: Dom sig)) 
   => HasLState i (dom  :: Dom sig)
instance (Monad (SigEffect sig), CInList i '(LStateLExp, LStateLVal) dom) 
      => HasLState i (dom :: Dom sig)

lstate :: forall i sig (dom :: Dom sig) g s t.
          HasLState i dom 
       => LExp dom g (s ⊸ s ⊗ t) -> LExp dom g (LState sig s t)
lstate = Dom (pfInList @_ @i @'(LStateLExp, LStateLVal)) . LState

applyLState :: forall i sig (dom :: Dom sig) g s t.
               HasLState i dom
            => LExp dom g (LState sig s t)
            -> LExp dom g (s ⊸ s ⊗ t)
applyLState e = 
  Dom (pfInList @_ @i @'(LStateLExp, LStateLVal)) $ ApplyLState e

vstate :: forall i sig (dom :: Dom sig) g s t.
          HasLState i dom
       => LVal dom (s ⊸ s ⊗ t) -> LVal dom (LState sig s t)
vstate = VDom (pfInList @_ @i @'(LStateLExp, LStateLVal)) . VState

lValToLState :: forall i sig (dom :: Dom sig) s t.
                HasLState i dom
             => LVal dom (LState sig s t) -> LStateLVal (LVal dom) (LState sig s t)
lValToLState (VDom pfInList' v) = 
  case compareInList (pfInList @_ @i @'(LStateLExp,LStateLVal)) pfInList' of
    Nothing   -> error "Value of type LState not derived from the LState domain"
    Just Dict -> v

instance HasLState i dom
      => Domain i LStateLExp LStateLVal (dom :: Dom sig) where

  valToExpDomain _ (VState v) = LState $ valToExp v

  substDomain _ pfA s (LState e) = lstate @i $ subst pfA s e
  substDomain _ pfA s (ApplyLState e) = applyLState @i $ subst pfA s e

  evalDomain _ (LState e) = do
    v <- eval' e
    return $ vstate @i v
  evalDomain _ (ApplyLState e) = do
    VState v <- fmap (lValToLState @i) $ eval' e
    return v


