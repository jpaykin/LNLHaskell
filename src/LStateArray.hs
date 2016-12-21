{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module LStateArray where

import Types
import Lang
import LState
import Arrays hiding (fromList, fromList', toList, toList')

type LStateArraySig  = '(IO, '[ LStateSig, ArraySig ])
type LStateArrayDomain = ( '[ ArrayDom, LStateDom ] :: Dom LStateArraySig )

--instance HasLStateSig '(IO,LStateArraySig) where
--  type LState s = 'Sig ('AndTy1 ('LStateSig s))

--instance HasArrayType LStateArraySig where
--  type Array a = 'Sig ('AndTy2 ('ArraySig a))

