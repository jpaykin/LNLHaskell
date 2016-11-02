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

