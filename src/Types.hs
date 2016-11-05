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
  One    :: LType
  Lolli  :: LType -> LType -> LType
  Lower  :: * -> LType
  Tensor :: LType -> LType -> LType
  With   :: LType -> LType -> LType
  Plus   :: LType -> LType -> LType

type (⊸) = Lolli
infixr 0 ⊸

type s ⊗ t = Tensor s t
infixr 3 ⊗

type s & t = With s t
infixr 3 &

type s ⊕ t = Plus s t
infixr 3 ⊕


type Ident = Nat
data Usage = Used LType | Unused
type Var = (Ident,Usage)
type Ctx = [Usage]

data SUsage :: Usage -> * where
  SUsed   :: forall s. SUsage ('Used s)
  SUnused :: SUsage 'Unused

data SCtx :: Ctx -> * where
  SNil  :: SCtx '[]
  SCons :: SUsage u -> SCtx g -> SCtx (u ': g)

data SSUsage where
   SSUsage :: SUsage u -> SSUsage
data SSCtx where
   SSCtx :: SCtx g -> SSCtx


-- Nats ---------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord)

data SIdent :: Nat -> * where
  SZ :: SIdent 'Z
  SS :: SIdent x -> SIdent ('S x)

instance Num Nat where
  Z   + n   = n
  S m + n   = S (m+n)
  Z   - n   = Z
  m   - Z   = m
  S m - S n = m - n
  Z   * n   = Z
  S m * n   = m * n + n
  abs e     = e
  signum e  = S Z
  fromInteger = undefined
  negate e    = undefined

toInt :: Nat -> Int
toInt Z = 0
toInt (S n) = toInt n + 1

instance Show Nat where
  show n = show $ toInt n
