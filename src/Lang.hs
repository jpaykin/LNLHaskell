{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds
#-}

module Lang where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe
import Debug.Trace
import GHC.TypeLits (Symbol(..))

import Prelim
import Types
import Classes


--Deep embedding

