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
  One   :: LType
  Tensor :: LType -> LType -> LType
  Lolli :: LType -> LType -> LType
  Lower :: * -> LType
type s ⊸ t = Lolli s t
infixr 0 ⊸
type s ⊗ t = Tensor s t
infixr 3 ⊗


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

{-
toSSUsage (Used s) = SSUsage SUsed
toSSUsage Unused   = SSUsage SUnused

toSSCtx :: Ctx -> SSCtx
toSSCtx []    = SSCtx SNil
toSSCtx (u:g) = 
  case (toSSCtx g, toSSUsage u) of
    (SSCtx g',SSUsage u') -> SSCtx $ SCons u' g'
-}



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
