{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module FrameClass where

import Data.Kind
import Data.Constraint

import Types
import Frame

-- InsertFrame ------------------------------------------------

type family AddFrame (f1::Frame) (x::Ident) (f2::Frame) :: Frame where
  AddFrame '[] x f2 = x ': f2
  AddFrame (y ': f1) x f2 = y ': AddFrame f1 x f2

class CAddFrame f1 x f2 f | f1 x f2 -> f where
  addFrame :: Dict (f ~ AddFrame f1 x f2)

instance CAddFrame '[] x f2 (x ': f2) where
  addFrame = Dict
instance CAddFrame f1 x f2 f => CAddFrame (y ': f1) x f2 (y ': f) where
  addFrame = case addFrame @f1 @x @f2 of Dict -> Dict



-- Well-formed context ------------------------------------------

class CWfCtx f g | g -> f where
  wfCtx :: WfCtx f g

instance CWfCtx '[] '[] where
  wfCtx = WfNil
instance CWfCtx f g => CWfCtx (x ': f) ('(x,'Used s) ': g) where
  wfCtx = WfUsed wfCtx
instance CWfCtx f g => CWfCtx (x ': f) ('(x,'Unused) ': g) where
  wfCtx = WfUnused wfCtx

-- Empty Context ------------------------------------------------

class CEmptyCtx f g | f -> g where
  emptyCtx :: EmptyCtx f g

instance CEmptyCtx '[] '[] where
  emptyCtx = EmptyNil
instance CEmptyCtx f g => CEmptyCtx (x ': f) ('(x, 'Unused) ': g) where
  emptyCtx = EmptyCons emptyCtx

-- Add To Context ----------------------------------------------

class CAddCtx x s f1 f2 g g' | x s f1 f2 g -> g' where
  addCtx :: AddCtx x s f1 f2 g g'

instance CWfCtx f g => CAddCtx x s '[] f ('(x,'Unused) ': g) ('(x,'Used s) ': g) where
  addCtx = AddHere wfCtx
instance CAddCtx x s f1 f2 g g' => CAddCtx x s (y ': f1) f2 ('(y,u) ': g) ('(y,u) ': g') where
  addCtx = AddLater addCtx

-- Singleton Context ------------------------------------------

class CSingletonCtx x s f1 f2 g | x s f1 f2 -> g where
  singletonCtx :: SingletonCtx x s f1 f2 g

instance CEmptyCtx f g => CSingletonCtx x s '[] f ( '(x,'Used s) ': g) where
  singletonCtx = AddHereS emptyCtx
instance CSingletonCtx x s f1 f2 g => CSingletonCtx x s (y ': f1) f2 ('(y,'Unused) ': g) where
  singletonCtx = AddLaterS singletonCtx


-- Merge ----------------------------------------------------

class CMerge g1 g2 g3 | g1 g2 -> g3 where
  merge :: Merge g1 g2 g3

instance CMerge '[] '[] '[] where
  merge = MergeE
instance CMerge g1 g2 g3 
      => CMerge ('(x,'Used t) ': g1) ('(x,'Unused) ': g2) ('(x,'Used t) ': g3) where
  merge = MergeL merge
instance CMerge g1 g2 g3 
      => CMerge ('(x,'Unused) ': g1) ('(x,'Used t) ': g2) ('(x,'Used t) ': g3) where
  merge = MergeR merge
instance CMerge g1 g2 g3 
      => CMerge ('(x,'Unused) ': g1) ('(x,'Unused) ': g2) ('(x,'Unused) ': g3) where
  merge = MergeU merge
