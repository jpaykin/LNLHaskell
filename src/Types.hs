{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase
#-}

module Types where

import Data.Kind
import Data.Constraint


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

data Nat = Z | S Nat deriving (Eq, Ord)

type family Plus m n :: Nat where
  Plus 'Z n = n
  Plus ('S m) n = 'S (Plus m n)
