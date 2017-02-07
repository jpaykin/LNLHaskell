{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase
#-}

module Types where

import Prelim

import Data.Kind

-- A signature consists of a monad (in which evaluation will occur) and a list
-- of type constructors. This way, a signature can be extended
-- semlessly by adding a new type constructor to the signature.
-- A type constructor (of type Sig -> *) is a way to extend the syntax of LTypes.
-- e.g. 
--      data LolliSig sig = LolliSig (LType sig) (LType sig)
data Sig = Sig (* -> *) [Sig -> *]

-- SigEffect and SigType project out the monad and constructors, respectively
type family SigEffect (sig :: Sig) :: * -> * where
  SigEffect ('Sig m _) = m
type family SigType (sig :: Sig) :: [Sig -> *] where
  SigType ('Sig _ tys) = tys


data LType (sig :: Sig) where
  LType :: InList ty (SigType sig) -> ty sig -> LType sig


-- In lists ------------------------------------------------------

-- Type class that searches for a proof that ty is a type constructor in sig
class CInSig (ty :: Sig -> *) (sig :: Sig)
instance CInSig' (GetIndex ty (SigType sig)) ty sig => CInSig ty sig

class CInSig' (i :: Nat) (ty :: Sig -> *) (sig :: Sig)
instance CInSig' 'Z ty ('Sig m (ty ': tys))
instance CInSig' i  ty ('Sig m tys) => CInSig' ('S i) ty ('Sig m (ty' ': tys))

-- The type InSig ty sig computes a type-level proof that ty ∈ sig
-- (if it exists)
type InSig (ty :: Sig -> *) sig = 
    (IsInList ty (SigType sig) :: InList ty (SigType sig))


-- Disjoint nats --------------------------------------

data Disjoint :: Nat -> Nat -> * where
  DisjointZS :: Disjoint 'Z ('S n) 
  DisjointSZ :: Disjoint ('S n) 'Z
  DisjointSS :: Disjoint m n -> Disjoint ('S m) ('S n)



