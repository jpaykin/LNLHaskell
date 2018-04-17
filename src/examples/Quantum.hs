{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds, LambdaCase,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors 
                               -fno-warn-name-shadowing #-}

module Quantum where

--import Data.Kind
--import Control.Applicative
--import Data.Typeable
import Prelude hiding ((^))
--import Data.Singletons
--import Numeric.LinearAlgebra hiding (toInt) -- hmatrix library
import GHC.TypeLits


import Prelim hiding (One)
import Types
import Interface
import DeepEmbedding

import LinTrans2 hiding (cnot)

-- Signature
data QuantumSig exp = MkQubit
type Qubit = MkLType MkQubit


class HasMILL exp => HasQuantum exp where
  new :: Bool -> exp '[] Qubit
  meas :: exp γ Qubit -> exp γ (Lower Bool)
  unitary :: KnownType σ => Unitary σ -> exp γ σ -> exp γ σ

controlBy :: (HasQuantum exp,KnownType σ) 
          => Unitary σ -> exp γ (Qubit ⊗ σ) -> exp γ (Qubit ⊗ σ)
controlBy u e = unitary (control u) e

-- -- first element is the control
cnot :: HasQuantum exp
     => exp γ (Qubit ⊗ Qubit) -> exp γ (Qubit ⊗ Qubit)
cnot = controlBy PauliX



-------------------------------------------------------
-- Deep embedding -------------------------------------
-------------------------------------------------------

type instance Effect Deep = DensityMonad
data instance LVal Deep Qubit = QId Int

  
data QuantumExp :: Sig -> Sig where
  New     :: Bool -> QuantumExp exp '[] Qubit
  Meas    :: exp γ Qubit -> QuantumExp exp γ (Lower Bool)
  Unitary :: KnownType σ => Unitary σ -> exp γ σ -> QuantumExp exp γ σ

instance HasQuantum Deep where
  new = Dom . New
  meas = Dom . Meas
  unitary u = Dom . Unitary u

instance Domain Deep QuantumExp where
  evalDomain (New b) _ = QId <$> newM b
  evalDomain (Meas e) ρ = do QId i <- eval e ρ
                             VPut <$> measM i
  evalDomain (Unitary u e) ρ = do v <- eval e ρ
                                  applyU u v
                                  return v

applyU :: forall σ. KnownType σ => Unitary σ -> LVal Deep σ -> DensityMonad ()
applyU u v = applyMatrix (interpU u) (valToQubits v)

class KnownType σ where
  numQubits :: Int
  valToQubits :: LVal Deep σ -> [Int]
instance KnownType Qubit where
  numQubits = 1
  valToQubits (QId i) = [i]
instance KnownType One where
  numQubits = 1
  valToQubits VUnit = []
instance (KnownType σ1,KnownType σ2) => KnownType (σ1 ⊗ σ2) where
  numQubits = numQubits @σ1 + numQubits @σ2
  valToQubits (VPair v1 v2) = valToQubits v1 ++ valToQubits v2
instance KnownType (Lower α) where
  numQubits = 0
  valToQubits (VPut _) = []



instance Show (Unitary σ) where
  show Identity = "I"
  show Hadamard = "H"
  show PauliX   = "X"
  show PauliY   = "Y"
  show PauliZ   = "Z"
  show (R m)    = "R " ++ show m
  show (Alt u0 u1) = "(" ++ show u0 ++ " ⊕ " ++ show u1 ++ ")"
  show (Transpose u) = show u ++ "†"
-- instance Show (QuantumLExp lang g τ) where
--   show (New b)  = "New(" ++ show b ++ ")"
--   show (Meas q) = "Meas(" ++ show q ++ ")"
--   show (Unitary u e) = "Unitary (" ++ show u ++ ") " ++ show e
-- --  show (ControlBy _ e e') = show e ++ "`ControlBy`" ++ show e'

-- Quantum Data

-- Add more?
data Unitary (σ :: LType) where
  Identity  :: KnownType σ => Unitary σ
  Hadamard  :: Unitary Qubit
  PauliX    :: Unitary Qubit -- (NOT)
  PauliY    :: Unitary Qubit
  PauliZ    :: Unitary Qubit
  R         :: Int -> Unitary Qubit
  Alt       :: KnownType σ => Unitary σ -> Unitary σ -> Unitary (Qubit ⊗ σ)
  Transpose :: Unitary σ -> Unitary σ

control :: KnownType σ  => Unitary σ -> Unitary (Qubit ⊗ σ)
control = Alt Identity

{-
type KnownQubits σ = SingI (NumQubits σ)

unitarySing :: forall σ. Unitary σ -> Sing (NumQubits σ)
unitarySing Identity = sing
unitarySing Hadamard = one
unitarySing PauliX   = one
unitarySing PauliY   = one
unitarySing PauliZ   = one
unitarySing (R _)    = one
unitarySing (Alt u0 _)    = SS $ unitarySing u0
unitarySing (Transpose u) = unitarySing u
-}






-- instance HasQuantumEffect ('Sig DensityMonad sigs) where
-- --  type QUnitary ('Sig DensityMonad sigs) = Density
--type QUnitary σ = Squared (NumQubits σ)

interpU :: forall σ. KnownType σ => Unitary σ -> Matrix
interpU Identity = ident $ numQubits @σ
interpU Hadamard = hadamard
interpU PauliX   = pauliX
interpU PauliY   = pauliY
interpU PauliZ   = pauliZ
interpU (R m)    = undefined -- rotation about the z axis by 2πi/2^m?
interpU (Alt (u0 :: Unitary σ') u1) =
    (newD False `kron` interpU u0) + (newD True `kron` interpU u1)
interpU (Transpose u) = transpose $ interpU u

type family   NumQubits (τ :: LType) :: Nat 
type instance NumQubits One            = 0
type instance NumQubits Qubit          = 1
type instance NumQubits (τ1 ⊗ τ2) = NumQubits τ1 + NumQubits τ2

{-
instance HasQuantumDom lang => Domain QuantumDom (lang :: Lang sig) where

  evalDomain _ (New b)   = do
    i <- newQubit @sig b
    return $ vqubit i
  evalDomain ρ (Meas e)  = do
    VQubit i <- toDomain @QuantumDom <$> eval' ρ e
    b <- measQubit @sig i
    return $ vput b
  evalDomain ρ (Unitary u e) = do
    v  <- eval' ρ e
    qs <- valToQubits @sig v
    applyU @sig u qs
    return v 
    
type Qubits (τ :: LType sig) = [QId]

valToQubits :: forall sig (lang :: Lang sig) τ.
              HasQuantumDom lang => LVal lang τ -> SigEffect sig (Qubits τ)
valToQubits v = case toDomain' @QuantumDom v of
    Just (VQubit i) -> return [i]
    Nothing -> case toDomain' @OneDom v of
      Just VUnit -> return []
      Nothing -> case toDomain' @TensorDom v of
        Just (VPair v1 v2) -> liftA2 (++) (valToQubits v1) (valToQubits v2)
        Nothing -> return [] 
--        case fromLVal' proxyLower v of
--          Just (VPut _) -> return []
--          Nothing       -> error "Cannot extract qubits from the given value"

type family   NumQubits (τ :: LType sig) :: Nat 
type instance NumQubits ('LType _ 'OneSig)            = 'Z
type instance NumQubits ('LType _ 'QubitSig)          = 'S 'Z
type instance NumQubits ('LType _ ('TensorSig τ1 τ2)) = NumQubits τ1 `Plus` NumQubits τ2
-}

--type instance NumQubits ('LType _ ('PlusSig τ1 τ2))   = NumQubits τ1 `Plus` NumQubits τ2
type instance NumQubits (Lower _)      = 0
  
-- EXAMPLES


-- Flip -------------------------------------------


qflip :: Lin Deep Bool
qflip = suspend $ meas (unitary Hadamard (new False))

-- ----------------------------------------------------
-- -- Teleportation -----------------------------------
-- ----------------------------------------------------

plus_minus :: HasQuantum exp => Bool -> Lift exp Qubit
plus_minus b = suspend $ unitary Hadamard $ new b

share :: HasQuantum exp => Lift exp (Qubit ⊸ Qubit ⊗ Qubit)
share = suspend . λ $ \q -> cnot (q ⊗ new False)

bell00 :: HasQuantum exp => Lift exp (Qubit ⊗ Qubit)
bell00 = suspend $ force (plus_minus False) `letin` \a ->
                   force share ^ a

alice :: HasQuantum exp => Lift exp (Qubit ⊸ Qubit ⊸ Lower (Bool,Bool))
alice = suspend . λ $ \q -> λ $ \a ->
            cnot (q ⊗ a) `letPair` \(q,a) ->
            meas (unitary Hadamard q) >! \x ->
            meas a >! \y ->
            put (x,y)
    
bob :: HasQuantum exp => Bool -> Bool -> Lift exp (Qubit ⊸ Qubit)
bob x y = suspend . λ $ \b ->
    if y then unitary PauliX b else b `letin` \b ->
    if x then unitary PauliZ b else b

teleport :: HasQuantum exp => Lift exp (Qubit ⊸ Qubit)
teleport = suspend . λ $ \q ->
    force bell00 `letPair` \(a,b) ->
    force alice ^ q ^ a >! \(x,y) ->
    force (bob x y) ^ b

teleport0 :: Lin Deep Bool
teleport0 = suspend . meas $ force teleport ^ new False


main' :: Lin Deep Bool
main' = suspend $ force bell00 `letPair` \(q1,q2) ->
                 meas q1 >! \x ->
                 meas q2 >! \y ->
                 put (x == y)

main :: IO ()
main = print $ run main'


-- Dependent fourier transform

type family (σ :: LType) ⊗⊗ (n :: Nat) :: LType where
    σ ⊗⊗ n = CompareOrd (CmpNat n 1)
                        One                -- n = 0
                        σ                  -- n = 1
                        (σ ⊗ (σ ⊗⊗ (n-1))) -- n >= 2
--  σ ⊗⊗ Z = One
--  σ ⊗⊗ S Z = σ
--  σ ⊗⊗ (S (S n)) = σ ⊗ (σ ⊗⊗ S n)


{- TODO: fix
rotations :: forall (m :: Nat) (n :: Nat) exp. (HasQuantum exp)
          => Sing m -> Sing n -> Lift exp (Qubit ⊗⊗ S n ⊸ Qubit ⊗⊗ S n)
rotations _ SZ      = idL
rotations _ (SS SZ) = idL
rotations m (SS n'@(SS _)) = suspend . λpair $ \(c,qs) -> qs `letPair` \(q,qs') ->
    force (rotations m n') ^ (c ⊗ qs') `letPair` \(c,qs') ->
    controlBy (R $ 2 + toInt m - toInt n') (c ⊗ q) `letPair` \(c,q) ->
    c ⊗ (q ⊗ qs')

fourier :: forall n exp. (HasQuantum exp)
        => Sing n -> Lift exp (Qubit ⊗⊗ n ⊸ Qubit ⊗⊗ n)
fourier SZ = idL
fourier (SS SZ) = suspend . λ $ unitary Hadamard
fourier (SS n'@(SS _)) = Suspend . λpair $ \(q,w) ->
        force (fourier n') ^ w `letin` \w -> 
        force (rotations (SS n') n') ^ (q ⊗ w)
-}
