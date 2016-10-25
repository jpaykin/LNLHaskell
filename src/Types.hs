{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, DeriveLift, StandaloneDeriving
#-}

module Types where

import Data.Kind
import Data.Constraint
import Language.Haskell.TH.Syntax


data LType where
  Lolli :: LType -> LType -> LType
  Lower :: * -> LType
type s ⊸ t = Lolli s t
infixr 0 ⊸


type Ident = Nat
data Usage = Used LType | Unused
type Var = (Ident,Usage)
type Ctx = [Usage]


-- a frame is a list of all identifiers (free and bound) in a term.

-- Nats ---------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord, Lift)

type family Plus m n :: Nat where
  Plus 'Z n = n
  Plus ('S m) n = 'S (Plus m n)

data NatS :: Nat -> * where
  ZS :: NatS 'Z
  SS :: NatS n -> NatS ('S n)
deriving instance Lift (NatS n)

data NatSS where
  NatSS :: NatS n -> NatSS
