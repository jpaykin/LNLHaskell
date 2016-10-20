{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Types where

import Data.Kind
import Data.Constraint


data LType where
  Lolli :: LType -> LType -> LType
  Lower :: * -> LType
type s ⊸ t = Lolli s t
infixr 0 ⊸
-- fix associativity


--data Var = Used Nat LType | Unused Nat LType
-- data Used = Used LType
-- data Unused = Unused LType
type Ident = Nat
data Usage = Used LType | Unused
type Var = (Ident,Usage)


-- a frame is a list of all identifiers (free and bound) in a term.
type Frame = [Ident]
type Zipper = (Frame,Frame)
type Ctx = [Var]

-- Nats ---------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord)
