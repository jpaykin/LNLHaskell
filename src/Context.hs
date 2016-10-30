{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, DeriveLift, StandaloneDeriving
#-}

module Context where

import Data.Kind
import Data.Constraint
import Language.Haskell.TH.Syntax

import Types

-- Pattern Matching -----------------------------------------

data Pattern where
  PVar  :: Ident -> Pattern
  PTuple:: [Pattern] -> Pattern

data SPat :: Pattern -> * where
  MkVar   :: forall x. SPat ('PVar x)
  MkTuple :: SPats ps -> SPat (PTuple ps)

data SPats :: [Pattern] -> * where
  MkNil    :: SPats '[]
  MkCons   :: SPat p -> SPats ps -> SPats (p ': ps)

type family FreshCtx g :: Nat where
  FreshCtx '[] = 'Z
  FreshCtx ('Unused ': g) = 'Z
  FreshCtx ('Used _ ': g) = 'S (FreshCtx g)
  
-- Shift -----------------------------------------------------

data Shift :: Nat -> Ctx -> Ctx -> * where
  ShiftHere  :: Shift 'Z g ('Unused ': g)
  ShiftLater :: Shift n g g' -> Shift ('S n) (u ': g) (u ': g')
deriving instance Lift (Shift i g g')


-- Equivalent Contexts ------------------------------------------

data Equiv  :: Ctx -> Ctx -> * where
  EquivNil  :: Equiv '[] '[]
  EquivEL   :: EmptyCtx g -> Equiv '[] g
  EquivER   :: EmptyCtx g -> Equiv g '[]
  EquivCons :: Equiv g1 g2 -> Equiv (u ': g1) (u ': g2)
deriving instance Lift (Equiv g g')

data EquivEmpty  :: Ctx -> Ctx -> * where
  EquivENil  :: EquivEmpty '[] '[]
  EquivEEL   :: EmptyCtx g -> EquivEmpty '[] g
  EquivEER   :: EmptyCtx g -> EquivEmpty g '[]
  EquivECons :: EquivEmpty g1 g2 -> EquivEmpty ('Unused ': g1) ('Unused ': g2)
deriving instance Lift (EquivEmpty g g')



-- Empty Context ------------------------------------------------

data EmptyCtx :: Ctx -> * where
  EmptyNil  :: EmptyCtx '[]
  EmptyCons :: forall x g. EmptyCtx g -> EmptyCtx ('Unused ': g)
deriving instance Lift (EmptyCtx g)

-- Add To Context ----------------------------------------------

data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddEHere   :: AddCtx 'Z s '[]            '[ 'Used s ]
  AddHere    :: SCtx g -> AddCtx 'Z s ('Unused ': g) ('Used s ': g)
  AddELater  :: AddCtx x s '[] g -> AddCtx ('S x) s '[] ('Unused ': g)
  AddLater   :: AddCtx x s g g'  -> AddCtx ('S x) s (u ': g) (u ': g')
deriving instance Lift (AddCtx x s g g')

data AddPat :: Pattern -> LType -> Ctx -> Ctx -> * where
  AddVar  :: AddCtx x s g g' -> AddPat ('PVar x) s g g'
  AddTuple :: AddPats ps ts g g' -> AddPat (PTuple ps) (Tuple ts) g g'

data AddPats  :: [Pattern] -> [LType] -> Ctx -> Ctx -> * where
  AddPatsNil  :: SCtx g -> AddPats '[] '[] g g
  AddPatsCons :: AddPat p t g1 g2 -> AddPats ps ts g2 g3 -> AddPats (p ': ps) (t ': ts) g1 g3

-- Singleton Context ------------------------------------------

data SingletonCtx :: Nat -> LType -> Ctx -> * where
  AddHereS  :: SingletonCtx 'Z s '[ 'Used s ]
  AddLaterS :: SingletonCtx x s g
            -> SingletonCtx ('S x) s ('Unused ': g)
deriving instance Lift (SingletonCtx x s g)

type family Sing x s :: Ctx where
  Sing 'Z s = '[ 'Used s ]
  Sing ('S x) s = 'Unused ': Sing x s

-- Disjoint Patterns ------------------------------------

data Disjoint :: Ident -> Ident -> * where
  DisjointZS :: Disjoint 'Z ('S x)
  DisjointSZ :: Disjoint ('S x) 'Z
  DisjointS  :: Disjoint x y -> Disjoint ('S x) ('S y)

data DisjointCtx :: Ident -> Ctx -> * where
  DisjointNil  :: DisjointCtx x '[]
  DisjointHere :: DisjointCtx 'Z ('Unused ': g)
  DisjointLater :: DisjointCtx x g -> DisjointCtx ('S x) (u ': g)

data DisjointPatCtx :: Pattern -> Ctx -> * where
  DisjointPatIdentCtx :: DisjointCtx x g -> DisjointPatCtx ('PVar x) g
  DisjointPatTupleCtx :: DisjointPatsCtx ps g -> DisjointPatCtx ('PTuple ps) g

data DisjointPatsCtx  :: [Pattern] -> Ctx -> * where
  DisjointPatsCtxNil  :: DisjointPatsCtx '[] g
  DisjointPatsCtxCons :: DisjointPatCtx p g -> DisjointPatsCtx ps g -> DisjointPatsCtx (p ': ps) g

data DisjointPat :: Ident -> Pattern -> * where
  DisjointIdent :: Disjoint x y -> DisjointPat x ('PVar y)
  DisjointTup   :: DisjointPats x ps -> DisjointPat x ('PTuple ps)

data DisjointPats :: Ident -> [Pattern] -> * where
  DisjointPatsNil   :: DisjointPats x '[]
  DisjointPatsCons  :: DisjointPat x p -> DisjointPats x ps -> DisjointPats x (p ': ps)

data DisjointPatPat :: Pattern -> Pattern -> * where
  DisjointPatIdent :: DisjointPat x p -> DisjointPatPat ('PVar x) p
  DisjointPatTup   :: DisjointPatPats ps p -> DisjointPatPat ('PTuple ps) p

data DisjointPatPats :: [Pattern] -> Pattern -> * where
  DisjointPatPatsNil  :: DisjointPatPats '[] p
  DisjointPatPatsCons :: DisjointPatPat p1 p -> DisjointPatPats ps2 p -> DisjointPatPats (p1 ': ps2) p

-- Merge ----------------------------------------------------

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
deriving instance Lift (Merge g1 g2 g3)

-- Remove ------------------------------------------

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = 'Unused ': g
  Remove ('S x) (u ': g) = u ': Remove x g

type family RemovePat p g :: Ctx where
  RemovePat ('PVar x) g = Remove x g
  RemovePat ('PTuple ps) g = RemovePats ps g

type family RemovePats ps g :: Ctx where
  RemovePats '[] g = g
  RemovePats (p ': ps) g = RemovePat p (RemovePats ps g)

-- In -------------------------------

data In :: Nat -> LType -> Ctx -> * where
  InHere  :: SCtx g   -> In  'Z s ('Used s ': g)
  InLater :: In x s g -> In ('S x) s (u ': g)
deriving instance Lift (In x s g)

data InPat :: Pattern -> LType -> Ctx -> * where
  InVar   :: In x s g -> InPat (PVar x) s g
  InTuple :: InPats ps ts g -> InPat (PTuple ps) (Tuple ts) g

data InPats :: [Pattern] -> [LType] -> Ctx -> * where
  InNil :: InPats '[] '[] g
  InCons :: DisjointPatPats ps p
         -> InPat p t g
         -> InPats ps ts g
         -> InPats (p ': ps) (t ': ts) g

-- Not In ----------------------------------

data NotIn :: Nat -> Ctx -> * where
  NotInNil   :: NatS x -> NotIn x '[]
  NotInHere  :: SCtx g -> NotIn 'Z ('Unused ': g)
  NotInLater :: NotIn x g -> NotIn ('S x) (u ': g)

type family AddFun x s g :: Ctx where
  AddFun x      s '[]            = Sing x s
  AddFun 'Z     s ('Unused ': g) = 'Used s ': g
  AddFun ('S x) s (u ': g)       = u ': AddFun x s g

-- Relation between In and Shift

type family InShift x n :: Nat where
  InShift ('S x) 'Z     = x
  InShift 'Z     ('S n) = 'Z
  InShift ('S x) ('S n) = 'S (InShift x n)

type family InUnshift x i :: Nat where
  InUnshift x      'Z     = 'S x
  InUnshift 'Z     ('S i) = 'Z
  InUnshift ('S x) ('S i) = 'S (InUnshift x i)

