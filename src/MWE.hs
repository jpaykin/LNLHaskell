{-# LANGUAGE TypeOperators, KindSignatures, DataKinds, TypeInType, TypeFamilies
#-}

module MWE where

import Data.Kind
import Prelim


type Sig = (Type -> Type, [Type -> Type])

type family SigEffect (sig :: Sig) :: Type -> Type where
  SigEffect '(m,_) = m
type family SigType (sig :: Sig) :: [Type -> Type] where
  SigType '(_,tys) = tys

data LType (sig :: Sig) where
  LType :: InSig ty sig -> ty (LType sig) -> LType sig
