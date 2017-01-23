{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase
#-}

module Types where

import Prelim

import Data.Kind
import Data.Constraint

type EffectSig = * -> *
type TypeSig = * -> *
type Sig = (EffectSig, [TypeSig])
type family SigEffect (sig :: Sig) :: EffectSig where
  SigEffect '(m,_) = m
type family SigType (sig :: Sig) :: [TypeSig] where
  SigType '(_,tys) = tys


data LType (sig :: Sig) where
  Sig    :: InList ty (SigType sig) -> ty (LType sig) -> LType sig


-- In lists ------------------------------------------------------

class CInSig (ty :: TypeSig) (sig :: Sig)
instance CInSig' (GetIndex ty (SigType sig)) ty sig => CInSig ty sig

class CInSig' (i :: Nat) (ty :: TypeSig) (sig :: Sig)
instance CInSig' 'Z ty '(m,ty ': tys)
instance CInSig' i ty '(m,tys) => CInSig' ('S i) ty '(m, ty' ': tys)


type Sig' (ty :: TypeSig) (tys :: [TypeSig]) = ('Sig (IsInList ty tys) 
            :: ty (LType '(m,tys)) -> LType '(m,tys))

type InSig (ty :: TypeSig) sig = 
    (IsInList ty (SigType sig) :: InList ty (SigType sig))


-- Disjoint nats --------------------------------------

data Disjoint :: Nat -> Nat -> * where
  DisjointZS :: Disjoint 'Z ('S n) 
  DisjointSZ :: Disjoint ('S n) 'Z
  DisjointSS :: Disjoint m n -> Disjoint ('S m) ('S n)





