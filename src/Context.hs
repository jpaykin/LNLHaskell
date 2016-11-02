{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Context where

import Data.Kind
import Data.Constraint

import Types


-- Fresh variable ------------------------------------------



-- Shift -----------------------------------------------------

data Shift :: Nat -> Ctx -> Ctx -> * where
  ShiftHere  :: Shift 'Z g ('Unused ': g)
  ShiftLater :: Shift n g g' -> Shift ('S n) (u ': g) (u ': g')


-- Equivalent Contexts ------------------------------------------

data Equiv  :: Ctx -> Ctx -> * where
  EquivNil  :: Equiv '[] '[]
  EquivEL   :: EmptyCtx g -> Equiv '[] g
  EquivER   :: EmptyCtx g -> Equiv g '[]
  EquivCons :: Equiv g1 g2 -> Equiv (u ': g1) (u ': g2)

data EquivEmpty  :: Ctx -> Ctx -> * where
  EquivENil  :: EquivEmpty '[] '[]
  EquivEEL   :: EmptyCtx g -> EquivEmpty '[] g
  EquivEER   :: EmptyCtx g -> EquivEmpty g '[]
  EquivECons :: EquivEmpty g1 g2 -> EquivEmpty ('Unused ': g1) ('Unused ': g2)


-- Empty Context ------------------------------------------------

data EmptyCtx :: Ctx -> * where
  EmptyNil  :: EmptyCtx '[]
  EmptyCons :: forall x g. EmptyCtx g -> EmptyCtx ('Unused ': g)


-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddEHere   :: AddCtx 'Z s '[]            '[ 'Used s ]
  AddHere    :: SCtx g -> AddCtx 'Z s ('Unused ': g) ('Used s ': g)
  AddELater  :: AddCtx x s '[] g -> AddCtx ('S x) s '[] ('Unused ': g)
  AddLater   :: AddCtx x s g g'  -> AddCtx ('S x) s (u ': g) (u ': g')


-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
data SingletonCtx :: Nat -> LType -> Ctx -> * where
  AddHereS  :: SingletonCtx 'Z s '[ 'Used s ]
  AddLaterS :: SingletonCtx x s g
            -> SingletonCtx ('S x) s ('Unused ': g)



-- Merge ----------------------------------------------------

-- merge g1 g2 g3
data Merge :: Ctx -> Ctx -> Ctx -> * where
  MergeE  :: Merge '[] '[] '[]
  MergeEL :: Merge '[] g g
  MergeER :: Merge g '[] g
  MergeL :: Merge g1 g2 g3 
         -> Merge ('Used t ': g1) ('Unused ': g2) ('Used t ': g3)
  MergeR :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Used t ': g2) ('Used t ': g3)
  MergeU :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Unused ': g2) ('Unused ': g3)


-- Remove ------------------------------------------

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = 'Unused ': g
  Remove ('S x) (u ': g) = u ': Remove x g


-- In -------------------------------

data In :: Nat -> LType -> Ctx -> * where
  InHere  :: SCtx g   -> In  'Z s ('Used s ': g)
  InLater :: In x s g -> In ('S x) s (u ': g)



-- Relation between In and Shift

type family InShift x n :: Nat where
  InShift ('S x) 'Z     = x
  InShift 'Z     ('S n) = 'Z
  InShift ('S x) ('S n) = 'S (InShift x n)


