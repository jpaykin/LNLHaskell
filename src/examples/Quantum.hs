{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-name-shadowing #-}

module Quantum where

import Data.Kind
import Data.Proxy
import Control.Applicative
import Data.Singletons
--import Numeric.LinearAlgebra hiding (toInt) -- hmatrix library

import Prelim
import Types
import Context
--import Proofs
import Lang
--import Classes
import Interface

--import Density hiding (cnot)
import LinTrans

-- Signature
data QuantumSig sig  = QubitSig
type Qubit = ('LType (IsInList QuantumSig (SigType sig))
                     ('QubitSig :: QuantumSig sig) :: LType sig)

data QuantumLVal (lang :: Lang sig) :: LType sig -> * where
  -- qubit identifier 
  VQubit :: QId -> QuantumLVal lang Qubit
  
data QuantumLExp (lang :: Lang sig) :: Ctx sig -> LType sig -> * where
  New     :: Bool -> QuantumLExp lang 'Empty Qubit
  Meas    :: LExp lang g Qubit -> QuantumLExp lang g (Lower Bool)
  Unitary :: Unitary σ -> LExp lang g σ -> QuantumLExp lang g σ
  -- control the first expression BY the second expression
  -- only valid if the first expression represents a unitary transformation
--  ControlBy :: Merge g1 g2 g 
--            -> LExp lang g1 σ -> LExp lang g2 Qubit -> QuantumLExp lang g (σ ⊗ Qubit)

type QuantumDom = '(QuantumLExp,QuantumLVal)
proxyQuantum :: Proxy QuantumDom
proxyQuantum = Proxy

instance Show (Unitary σ) where
  show Hadamard = "H"
  show PauliX   = "X"
  show PauliY   = "Y"
  show PauliZ   = "Z"
  show _        = undefined
instance Show (QuantumLExp lang g τ) where
  show (New b)  = "New " ++ show b
  show (Meas q) = "Meas " ++ show q
  show (Unitary u e) = "Unitary (" ++ show u ++ ") " ++ show e
--  show (ControlBy _ e e') = show e ++ "`ControlBy`" ++ show e'

-- Quantum Data

-- Add more?
data Unitary (σ :: LType sig) where
  Identity  :: KnownQubits σ => Unitary σ
  Hadamard  :: Unitary Qubit
  PauliX    :: Unitary Qubit -- (NOT)
  PauliY    :: Unitary Qubit
  PauliZ    :: Unitary Qubit
  Alt       :: Unitary σ -> Unitary σ -> Unitary (Qubit ⊗ σ)
  Transpose :: Unitary σ -> Unitary σ

type KnownQubits σ = SingI (NumQubits σ)

control :: KnownQubits σ  => Unitary σ -> Unitary (Qubit ⊗ σ)
control = Alt Identity

type QId = Int
class Monad (SigEffect sig) => HasQuantumEffect sig where
  type family QUnitary sig
  interpU :: forall (σ :: LType sig). Unitary σ -> QUnitary sig

  newQubit  :: Bool -> SigEffect sig QId
  applyU    :: forall (σ :: LType sig).
               Unitary σ -> Qubits σ -> SigEffect sig ()
  measQubit :: QId -> SigEffect sig Bool

instance HasQuantumEffect ('Sig DensityMonad sigs) where
  type QUnitary ('Sig DensityMonad sigs) = Density

  interpU :: forall (σ :: LType ('Sig DensityMonad sigs)). 
             Unitary σ -> QUnitary ('Sig DensityMonad sigs)
  interpU Identity = identD $ fromIntegral . toInt $ (sing :: Sing (NumQubits σ))
  interpU Hadamard = hadamard
  interpU PauliX   = pauliX
  interpU PauliY   = pauliY
  interpU PauliZ   = pauliZ
  interpU (Alt (u0 :: Unitary σ') u1)   = 
    (newD False `kronD` interpU u0) + (newD True `kronD` interpU u1)
  interpU (Transpose u) = transposeD $ interpU u

  newQubit  = newM
  applyU u  = applyUnitaryM (interpU u)
  measQubit = measM
  

-- Language instance

type HasQuantumDom (lang :: Lang sig) =
    ( HasQuantumEffect sig
    , WFDomain QuantumDom lang
    , WFDomain OneDom lang, WFDomain TensorDom lang, WFDomain LolliDom lang
    , WFDomain LowerDom lang)



instance HasQuantumDom lang => Domain QuantumDom (lang :: Lang sig) where

  evalDomain _ (New b)   = do
    i <- newQubit @sig b
    return $ vqubit i
  evalDomain ρ (Meas e)  = do
    VQubit i <- evalToValDom proxyQuantum ρ e
    b <- measQubit @sig i
    return $ vput b
  evalDomain ρ (Unitary u e) = do
    v  <- eval' ρ e
    qs <- valToQubits @sig v
    applyU @sig u qs
    return v 
    
type Qubits (τ :: LType sig) = [QId]
-- This type family should be open 
-- type family Qubits (τ :: LType sig) :: * 
-- type instance Qubits ('LType _ 'OneSig) = ()
-- type instance Qubits ('LType _ 'QubitSig) = QId
-- type instance Qubits ('LType _ ('TensorSig τ1 τ2)) = (Qubits τ1, Qubits τ2)
-- type instance Qubits ('LType _ ('LowerSig _)) = ()

valToQubits :: forall sig (lang :: Lang sig) τ.
              HasQuantumDom lang => LVal lang τ -> SigEffect sig (Qubits τ)
valToQubits v = case fromLVal' proxyQuantum v of 
    Just (VQubit i) -> return [i]
    Nothing -> case fromLVal' proxyOne v of
      Just VUnit -> return []
      Nothing -> case fromLVal' proxyTensor v of
        Just (VPair v1 v2) -> liftA2 (++) (valToQubits v1) (valToQubits v2)
        Nothing -> return [] 
--        case fromLVal' proxyLower v of
--          Just (VPut _) -> return []
--          Nothing       -> error "Cannot extract qubits from the given value"

type family   NumQubits (τ :: LType sig) :: Nat 
type instance NumQubits ('LType _ 'OneSig)            = 'Z
type instance NumQubits ('LType _ 'QubitSig)          = 'S 'Z
type instance NumQubits ('LType _ ('TensorSig τ1 τ2)) = NumQubits τ1 `Times` NumQubits τ2
type instance NumQubits ('LType _ ('PlusSig τ1 τ2))   = NumQubits τ1 `Plus` NumQubits τ2
type instance NumQubits ('LType _ ('LowerSig _))      = 'Z
  
-- Interface for quantum data

new :: HasQuantumDom lang
    => Bool -> LExp lang 'Empty Qubit
new = Dom proxyQuantum . New


meas :: HasQuantumDom lang
     => LExp lang g Qubit -> LExp lang g (Lower Bool)
meas = Dom proxyQuantum . Meas

unitary :: HasQuantumDom lang
        => Unitary σ -> LExp lang g σ -> LExp lang g σ
unitary u = Dom proxyQuantum . Unitary u

vqubit :: forall sig (lang :: Lang sig).
          HasQuantumDom lang
       => QId -> LVal lang Qubit
vqubit = VDom proxyQuantum . VQubit

controlBy :: (HasQuantumDom lang, KnownQubits σ)
          => Unitary σ -> LExp lang g (Qubit ⊗ σ) -> LExp lang g (Qubit ⊗ σ)
controlBy u e = unitary (control u) e

-- first element is the control
cnot :: HasQuantumDom lang => LExp lang g (Qubit ⊗ Qubit) -> LExp lang g (Qubit ⊗ Qubit)
cnot = controlBy PauliX

----------------------------------------------------
-- Teleportation -----------------------------------
----------------------------------------------------

plus_minus :: HasQuantumDom lang
           => Bool -> Lift lang Qubit
plus_minus b = Suspend $ unitary Hadamard $ new b

share :: HasQuantumDom lang
      => Lift lang (Qubit ⊸ Qubit ⊗ Qubit)
share = Suspend . λ $ \q ->
    cnot (q ⊗ new False)

bell00 :: HasQuantumDom lang
       => Lift lang (Qubit ⊗ Qubit)
bell00 = Suspend $
    force (plus_minus False) `letin` \a ->
    force share `app` a
    
alice :: HasQuantumDom lang
      => Lift lang (Qubit ⊸ Qubit ⊸ Lower (Bool, Bool))
alice = Suspend . λ $ \q -> λ $ \a -> 
            cnot (q ⊗ a) `letPair` \(q,a) ->
            meas (unitary Hadamard q) >! \x ->
            meas a >! \y ->
            put (x,y)

bob :: HasQuantumDom lang
    => (Bool,Bool) -> Lift lang (Qubit ⊸ Qubit)
bob (x,y) = Suspend . λ $ \b ->
    if y then unitary PauliX b else b `letin` \b ->
    if x then unitary PauliZ b else b 

teleport :: HasQuantumDom lang
         => Lift lang (Qubit ⊸ Qubit)
teleport = Suspend . λ $ \q ->
    force bell00 `letPair` \(a,b) ->
    force alice `app` q `app` a >! \(x,y) ->
    force (bob (x,y)) `app` b

teleport0 :: HasQuantumDom lang => Lin lang Bool
teleport0 = suspendL . meas $ force teleport `app` new False

qflip :: HasQuantumDom lang => Lin lang Bool
qflip = suspendL $ meas (unitary Hadamard (new False))
    
type MyQuantumSig = ( 'Sig DensityMonad (QuantumSig ': MELLSig) )
type MyQuantumLang = ( 'Lang (QuantumDom ': MELL) :: Lang MyQuantumSig )


