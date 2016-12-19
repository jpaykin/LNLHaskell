{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module LStateArray where

import Types
import LState
import Arrays
import Domain

type LStateArraySig  = (LStateSig :+: ArraySig :: TypeSig)

instance HasLStateSig '(IO,LStateArraySig) where
  type LState s = 'Sig ('AndTy1 ('LStateSig s))

--instance HasArrayType LStateArraySig where
--  type Array a = 'Sig ('AndTy2 ('ArraySig a))
