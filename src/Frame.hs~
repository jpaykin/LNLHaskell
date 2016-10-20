{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Frame where

import Data.Kind
import Data.Constraint

import Types

-- Well-formed context ------------------------------------------

data WfCtx :: Frame -> Ctx -> * where
  WfNil    :: WfCtx '[] '[]
  WfUsed   :: WfCtx f g -> WfCtx (x ': f) ('(x,'Used t) ': g)
  WfUnused :: WfCtx f g -> WfCtx (x ': f) ('(x,'Unused) ': g)

-- Empty Context ------------------------------------------------

data EmptyCtx :: Frame -> Ctx -> * where
  EmptyNil  :: EmptyCtx '[] '[]
  EmptyCons :: EmptyCtx f g -> EmptyCtx (x ': f) ('(x, 'Unused) ': g)


emptyUnique :: EmptyCtx f g -> EmptyCtx f g' -> Dict (g ~ g')
emptyUnique = undefined

-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
-- f1++[(x,t)]++f2 is a frame for g and g'
data AddCtx  :: Nat -> LType -> Frame -> Frame -> Ctx -> Ctx -> * where
  AddHere    :: WfCtx f g 
             -> AddCtx x t '[] f ('(x, 'Unused) ': g) ( '(x, 'Used t) ': g )
  AddLater   :: AddCtx x s f1 f2 g g' -> AddCtx x s (y ': f1) f2 ('(y,u) ': g) ('(y,u) ': g')

-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
-- f1++[(x,s)]++f2 is a frame for g
data SingletonCtx :: Nat -> LType -> Frame -> Frame -> Ctx -> * where
  AddHereS  :: EmptyCtx f g 
            -> SingletonCtx x s '[] f ( '(x,'Used s) ': g)
  AddLaterS :: SingletonCtx x s f1 f2 g 
            -> SingletonCtx x s (y ': f1) f2 ('(y, 'Unused) ': g)

-- Merge ----------------------------------------------------

-- merge g1 g2 g3
-- assuming g1 and g2 share a frame f, merge is functional.
data Merge :: Ctx -> Ctx -> Ctx -> * where
  MergeE :: Merge '[] '[] '[]
  MergeL :: Merge g1 g2 g3 
         -> Merge ('(x,'Used t) ': g1) ('(x,'Unused) ': g2) ('(x,'Used t) ': g3)
  MergeR :: Merge g1 g2 g3 
         -> Merge ('(x,'Unused) ': g1) ('(x,'Used t) ': g2) ('(x,'Used t) ': g3)
  MergeU :: Merge g1 g2 g3 
         -> Merge ('(x,'Unused) ': g1) ('(x,'Unused) ': g2) ('(x,'Unused) ': g3)


mergeEmpty3 :: forall f g. EmptyCtx f g -> Merge g g g
mergeEmpty3 EmptyNil = MergeE
mergeEmpty3 (EmptyCons pfEmpty) = MergeU (mergeEmpty3 pfEmpty)
