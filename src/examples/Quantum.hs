{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module Quantum where

import Data.Kind
import Data.Proxy
import Control.Applicative

import Prelim hiding (Z)
import Types
import Context
import Proofs
import Lang
import Classes
import Interface

import Density

-- Signature
data QuantumSig :: TypeSig where
  QubitSig :: QuantumSig ty
type Qubit = ('Sig (IsInList QuantumSig (SigType sig))
                   ('QubitSig :: QuantumSig (LType sig)) :: LType sig)

data QuantumLVal (lang :: Lang sig) :: LType sig -> * where
  -- qubit identifier 
  VQubit :: QId -> QuantumLVal lang Qubit
  
data QuantumLExp (lang :: Lang sig) :: Ctx sig -> LType sig -> * where
  Qubit   :: QId  -> QuantumLExp lang 'Empty Qubit
  New     :: Bool -> QuantumLExp lang 'Empty Qubit
  Meas    :: LExp lang g Qubit -> QuantumLExp lang g (Lower Bool)
  Unitary :: Unitary s -> LExp lang g s -> QuantumLExp lang g s
  -- control the first expression BY the second expression
  ControlBy :: Merge g1 g2 g 
            -> LExp lang g1 s -> LExp lang g2 Qubit -> QuantumLExp lang g (s ⊗ Qubit)

type QuantumDom = '(QuantumLExp,QuantumLVal)
proxyQuantum :: Proxy QuantumDom
proxyQuantum = Proxy

-- Quantum Data

-- Add more?
data Unitary (s :: LType sig) where
  Hadamard :: Unitary Qubit
--  CNOT     :: Unitary (Qubit ⊗ Qubit)
  Not      :: Unitary Qubit
  X        :: Unitary Qubit
  Z        :: Unitary Qubit

-- Quantum Simulation Class

type QId = Int
class Monad (SigEffect sig) => HasQuantumEffect sig where
  type family QUnitary (s :: LType sig)
  interpU :: forall (s :: LType sig). Unitary s -> QUnitary s

  newQubit  :: Bool -> SigEffect sig QId
  applyU    :: forall (s :: LType sig).
               Unitary s -> Qubits s -> SigEffect sig ()
  measQubit :: QId -> SigEffect sig Bool

instance HasQuantumEffect '(DensityMonad,sigs) where
  type QUnitary _ = Mat

  interpU Hadamard = (hadamard :: Mat)
--  interpU CNOT     = cnot

  newQubit  = undefined
  applyU    = undefined
  measQubit = undefined
  

-- Language instance

class (Domain OneDom lang, Domain TensorDom lang, Domain LowerDom lang,
       Domain QuantumDom lang, Domain LolliDom lang, HasQuantumEffect sig)
    => HasQuantumDom (lang :: Lang sig)
instance (Domain OneDom lang, Domain TensorDom lang, Domain LowerDom lang,
          Domain QuantumDom lang, Domain LolliDom lang, HasQuantumEffect sig)
       => HasQuantumDom (lang :: Lang sig)


instance HasQuantumDom lang => Language QuantumDom (lang :: Lang sig) where
  substDomain pfA s (Meas e) = meas $ subst pfA s e
  substDomain pfA s (Unitary u e) = unitary u $ subst pfA s e
--  substDomain pfA s (ControlBy pfM e1 e2) = 
--    case mergeAddSplit pfM pfA of
--      Left  (pfA1,pfM1) -> Dom proxyQuantum $ ControlBy pfM1 (subst pfA1 s e1) e2
--      Right (pfA2,pfM2) -> Dom proxyQuantum $ ControlBy pfM2 e1 (subst pfA2 s e2)

  valToExpDomain :: forall sig (lang :: Lang sig) (s :: LType sig).
                    QuantumLVal lang s
                 -> QuantumLExp lang 'Empty s
  valToExpDomain (VQubit i) = Qubit i

  -- Add controlBy
  evalDomain :: QuantumLExp lang 'Empty s -> SigEffect sig (LVal lang s)
  evalDomain (Qubit i) = return $ vqubit i
  evalDomain (New b)   = do
    i <- newQubit @sig b
    return $ vqubit i
  evalDomain (Meas e)  = do
    VQubit i <- evalToValDom proxyQuantum e
    b <- measQubit @sig i
    return $ vput b
  evalDomain (Unitary u e) = do
    v  <- eval' e
    qs <- valToQubits @sig v
    applyU @sig u qs
    return v 
    

-- This type family should be open 
type family Qubits (t :: LType sig) :: * 
type instance Qubits ('Sig _ 'OneSig) = ()
type instance Qubits ('Sig _ 'QubitSig) = QId
type instance Qubits ('Sig _ ('TensorSig t1 t2)) = (Qubits t1, Qubits t2)
type instance Qubits ('Sig _ ('LowerSig _)) = ()

valToQubits :: forall sig (lang :: Lang sig) t.
              HasQuantumDom lang => LVal lang t -> SigEffect sig (Qubits t)
valToQubits v = case fromLVal proxyQuantum v of 
    Just (VQubit i) -> return i
    Nothing -> case fromLVal proxyOne v of
      Just VUnit -> return ()
      Nothing -> case fromLVal proxyTensor v of
        Just (VPair v1 v2) -> liftA2 (,) (valToQubits v1) (valToQubits v2)
        Nothing -> case fromLVal proxyLower v of
          Just (VPut _) -> return ()
          Nothing       -> error "Cannot extract qubits from the given value"
    
  



-- Interface for quantum data

new :: HasQuantumDom lang
    => Bool -> LExp lang 'Empty Qubit
new = Dom proxyQuantum . New


meas :: HasQuantumDom lang
     => LExp lang g Qubit -> LExp lang g (Lower Bool)
meas = Dom proxyQuantum . Meas

unitary :: HasQuantumDom lang
        => Unitary s -> LExp lang g s -> LExp lang g s
unitary u = Dom proxyQuantum . Unitary u

vqubit :: forall sig (lang :: Lang sig).
          HasQuantumDom lang
       => QId -> LVal lang Qubit
vqubit = VDom proxyQuantum . VQubit

controlBy :: (HasQuantumDom lang, CMerge g1 g2 g)
          => LExp lang g1 s -> LExp lang g2 Qubit -> LExp lang g (s ⊗ Qubit)
controlBy e1 e2 = Dom proxyQuantum $ ControlBy merge e1 e2



----------------------------------------------------
-- Teleportation -----------------------------------
----------------------------------------------------

plus_minus :: HasQuantumDom lang
           => Bool -> Lift lang Qubit
plus_minus b = Suspend $ unitary Hadamard $ new b

share :: HasQuantumDom lang
      => Lift lang (Qubit ⊸ Qubit ⊗ Qubit)
share = Suspend . λ $ \q ->
    new False `controlBy` var q

bell00 :: HasQuantumDom lang
       => Lift lang (Qubit ⊗ Qubit)
bell00 = Suspend $
    force (plus_minus False) `letin` \a ->
    force share `app` var a
    
alice :: HasQuantumDom lang
      => Lift lang (Qubit ⊸ Qubit ⊸ Lower (Bool, Bool))
alice = Suspend . λ $ \q -> λ $ \a ->
    unitary Not (var a) `controlBy` var q `letPair` \(a,q) ->
    meas (unitary Hadamard $ var q) >! \x ->
    meas (var a) >! \y ->
    put (x,y)

bob :: HasQuantumDom lang
    => (Bool,Bool) -> Lift lang (Qubit ⊸ Qubit)
bob (x,y) = Suspend . λ $ \b ->
    if y then unitary X (var b) else var b `letin` \b ->
    if x then unitary Z (var b) else var b 

teleport :: HasQuantumDom lang
         => Lift lang (Qubit ⊸ Qubit)
teleport = Suspend . λ $ \q ->
    force bell00 `letPair` \(a,b) ->
    force alice `app` var q `app` var a >! \(x,y) ->
    force (bob (x,y)) `app` var b
    
