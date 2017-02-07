{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module RefCells where

import Data.STRef 
import Data.IORef
import Data.Proxy

import Types
import Context
import Lang
import Interface
import Proofs
import Classes

data RefSig sig = RefSig (LType sig)
type Ref σ = ('LType (InSig RefSig sig) ('RefSig σ) :: LType sig)

data RefLExp lang γ τ where
  New :: LExp lang γ τ -> RefLExp lang γ (Ref τ)
  Update :: Merge γ1 γ2 γ 
         -> LExp lang γ1 (σ ⊸ σ ⊗ τ) -> LExp lang γ2 (Ref σ) 
         -> RefLExp lang γ (Ref σ ⊗ τ)
data RefLVal lang τ where
  VRef :: IORef (LVal lang τ) -> RefLVal lang (Ref τ)

type RefDom = '(RefLExp, RefLVal)
proxyRef = (Proxy :: Proxy RefDom)
type HasRefDom (lang :: Lang sig) = ( SigEffect sig ~ IO
                                    , WFDomain RefDom lang
                                    , Domain TensorDom lang
                                    , Domain LolliDom lang
                                    , Domain OneDom lang )

instance HasRefDom lang => Domain RefDom lang where
  evalDomain ρ (New e) = do
    v <- eval' ρ e
    vref <$> newIORef v
  evalDomain ρ (Update pfM f e) = do
      VRef r     <- evalToValDom proxyRef ρ2 e
      v          <- readIORef r
      VPair v' t <- fromLVal proxyTensor <$> evalApplyValue ρ1 f v
      writeIORef r v'
      return $ vref r `vpair` t
    where
      (ρ1,ρ2) = splitSCtx pfM ρ


new :: Domain RefDom lang => LExp lang γ τ -> LExp lang γ (Ref τ)
new = Dom proxyRef . New
update :: (Domain RefDom lang, CMerge γ1 γ2 γ)
       => LExp lang γ1 (σ ⊸ σ ⊗ τ)
       -> LExp lang γ2 (Ref σ) -> LExp lang γ (Ref σ ⊗ τ)
update f r = Dom proxyRef $ Update merge f r

vref :: Domain RefDom lang => IORef (LVal lang τ) -> LVal lang (Ref τ)
vref = VDom proxyRef . VRef

instance Show (RefLExp lang γ τ) where
  show _ = undefined
