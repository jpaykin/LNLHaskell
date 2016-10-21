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

-- Concatenate/splice an element into a pair of frames

type family Splice (f1 :: Frame) (x :: Ident) (f2 :: Frame) where
  Splice '[] x f2 = x ': f2
  Splice (y ': f1) x f2 = y ': Splice f1 x f2

data SpliceF :: Frame -> Ident -> Frame -> Frame -> * where
--  SpliceF :: Dict (Splice f1 x f2 ~ f) -> SpliceF f1 x f2 f
  SpliceEmpty :: SpliceF '[] x f2 (x ': f2)
  SpliceCons  :: SpliceF f1 x f2 f -> SpliceF (y ': f1) x f2 (y ': f2)



-- Well-formed context ------------------------------------------

data WfCtx :: Frame -> Ctx -> * where
  WfNil    :: WfCtx '[] '[]
  WfUsed   :: WfCtx f g -> WfCtx (x ': f) ('(x,'Used t) ': g)
  WfUnused :: WfCtx f g -> WfCtx (x ': f) ('(x,'Unused) ': g)


-- Empty Context ------------------------------------------------

data EmptyCtx :: Frame -> Ctx -> * where
  EmptyNil  :: EmptyCtx '[] '[]
  EmptyCons :: forall x f g. EmptyCtx f g -> EmptyCtx (x ': f) ('(x, 'Unused) ': g)


emptyUnique :: EmptyCtx f g -> EmptyCtx f g' -> Dict (g ~ g')
emptyUnique EmptyNil EmptyNil = Dict
emptyUnique (EmptyCons pf1) (EmptyCons pf2) = 
  case emptyUnique pf1 pf2 of Dict -> Dict

-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
-- f1++[(x,t)]++f2 is a frame for g and g'
data AddCtx  :: Nat -> LType -> Frame -> Frame -> Ctx -> Ctx -> * where
  AddHere    :: WfCtx f g 
             -> AddCtx x s '[] f ('(x, 'Unused) ': g) ( '(x, 'Used s) ': g )
  AddLater   :: AddCtx x s f1 f2 g g' 
             -> AddCtx x s (y ': f1) f2 ('(y,u) ': g) ('(y,u) ': g')

addCtxWf :: AddCtx x s f1 f2 g g' -> (WfCtx (Splice f1 x f2) g, WfCtx (Splice f1 x f2) g')
addCtxWf = undefined

type family Insert s f1 f2 g :: Ctx where
  Insert s '[]       f2 ('(x,'Unused) ': g) = '(x,'Used s) ': g
  Insert s (_ ': f1) f2 (v ': g)            = v ': Insert s f1 f2 g

-- swaping
addTwice :: Splice f1 x f2 ~ Splice f1' y f2'
         => AddCtx x s f1  f2  g1 g2
         -> AddCtx y t f1' f2' g2 g3
         -> (AddCtx y t f1' f2' g1 (Insert t f1' f2' g1), 
             AddCtx x s f1 f2 (Insert t f1' f2' g1) g3)
addTwice (AddHere pfWf)   (AddLater pfAdd)  = undefined
addTwice (AddLater pfAdd) (AddHere pfWf)    = undefined
addTwice (AddLater pfAdd) (AddLater pfAdd') = undefined

-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
-- f1++[(x,s)]++f2 is a frame for g
data SingletonCtx :: Nat -> LType -> Frame -> Frame -> Ctx -> * where
  AddHereS  :: EmptyCtx f g 
            -> SingletonCtx x s '[] f ( '(x,'Used s) ': g)
  AddLaterS :: SingletonCtx x s f1 f2 g 
            -> SingletonCtx x s (y ': f1) f2 ('(y, 'Unused) ': g)


addSingletonEmpty :: forall x s f1 f2 g g'. AddCtx x s f1 f2 g g' 
                  -> SingletonCtx x s f1 f2 g' 
                  -> EmptyCtx (Splice f1 x f2) g
addSingletonEmpty (AddHere pfWf)   (AddHereS pfEmpty) = EmptyCons @x pfEmpty
addSingletonEmpty (AddLater pfAdd) (AddLaterS pfSing) = 
                  EmptyCons $ addSingletonEmpty pfAdd pfSing

wfEmptyInv :: WfCtx f g -> EmptyCtx f' g -> Dict (f ~ f')
wfEmptyInv WfNil EmptyNil = Dict
wfEmptyInv (WfUnused pfWf) (EmptyCons pfEmpty) = 
  case wfEmptyInv pfWf pfEmpty of Dict -> Dict

addSingletonInv :: AddCtx x s f1 f2 g g' 
               -> SingletonCtx y t f1' f2' g' 
               -> Dict ('(x,s,f1,f2) ~ '(y,t,f1',f2'))
addSingletonInv (AddHere pfWf)   (AddHereS pfEmpty) = 
  case wfEmptyInv pfWf pfEmpty of Dict -> Dict
addSingletonInv (AddLater pfAdd) (AddLaterS pfSing) =
  case addSingletonInv pfAdd pfSing of Dict -> Dict

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

mergeEmpty :: forall f g1 g2 g. 
              Merge g1 g2 g 
           -> EmptyCtx f g 
           -> (EmptyCtx f g1, EmptyCtx f g2)
mergeEmpty MergeE       EmptyNil        = (EmptyNil, EmptyNil)
mergeEmpty (MergeU pfM) (EmptyCons pfE) = 
  let (pfE1, pfE2) = mergeEmpty pfM pfE 
  in (EmptyCons pfE1, EmptyCons pfE2)

type family Remove f1 f2 g :: Ctx where
  Remove '[]       f2 ('(x, u) ': g) = '(x, 'Unused) ': g
  Remove (_ ': f1) f2 ('(x, u) ': g) = '(x, u) ': Remove f1 f2 g


mergeAdd :: Merge g1 g2 g 
         -> AddCtx x s f1 f2 g0 g
         -> Either (AddCtx x s f1 f2 (Remove f1 f2 g1) g1, Merge (Remove f1 f2 g1) g2 g0)
                   (AddCtx x s f1 f2 (Remove f1 f2 g2) g2, Merge g1 (Remove f1 f2 g2) g0)
mergeAdd = undefined
