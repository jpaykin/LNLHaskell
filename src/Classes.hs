{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Classes where

import Data.Kind
import Data.Constraint

import Types
import Context

-- Singleton instances ----------------------------------

class KnownUsage u where
  usg :: SUsage u

instance KnownUsage 'Unused where
  usg = SUnused
instance KnownUsage ('Used s) where
  usg = SUsed @s

class KnownCtx g where
  ctx :: SCtx g

instance KnownCtx '[] where
  ctx = SNil
instance (KnownCtx g,KnownUsage u) => KnownCtx (u ': g) where
  ctx = SCons usg ctx


-- In Context ---------------------------------------------

class CIn x s g where
  inCtx :: In x s g

instance KnownCtx g => CIn 'Z s ('Used s ': g) where
  inCtx = InHere ctx
instance CIn x s g => CIn ('S x) s (u ': g) where
  inCtx = InLater inCtx

class CInPat p t g where
  inPat :: InPat p t g

instance CIn x s g => CInPat ('PVar x) s g where
  inPat = InVar inCtx
instance CInPats ps ts g => CInPat ('PTuple ps) ('Tuple ts) g where
  inPat = InTuple inPats

class CInPats ps ts g where
  inPats :: InPats ps ts g

instance CInPats '[] '[] g where
  inPats = InNil
instance (CDisjointPatPats ps p, CInPat p t g, CInPats ps ts g) => CInPats (p ': ps) (t ': ts) g where
  inPats = InCons disjointPatPats inPat inPats

-- Disjoint -----------------------------------------------

class CDisjointPatPats ps p where
  disjointPatPats :: DisjointPatPats ps p



-- Empty Context ------------------------------------------------

class CEmptyCtx g where
  emptyCtx :: EmptyCtx g

instance CEmptyCtx '[] where
  emptyCtx = EmptyNil
instance CEmptyCtx g => CEmptyCtx ('Unused ': g) where
  emptyCtx = EmptyCons emptyCtx

-- Add To Context ----------------------------------------------

class CAddCtx x s g g' | x s g -> g' where
  addCtx :: AddCtx x s g g'

instance KnownCtx g => CAddCtx 'Z s ('Unused ': g) ('Used s ': g) where
  addCtx = AddHere ctx
instance CAddCtx 'Z s '[] '[ 'Used s ] where
  addCtx = AddEHere
instance CAddCtx x s g g' => CAddCtx ('S x) s (u ': g) (u ': g') where
  addCtx = AddLater addCtx
instance CAddCtx x s '[] g' => CAddCtx ('S x) s '[] ('Unused ': g') where
  addCtx = AddELater addCtx


class CAddCtxRev x s g g' | x g' -> s g where
  addCtxRev :: AddCtx x s g g'

instance KnownCtx g => CAddCtxRev 'Z s ('Unused ': g) ('Used s ': g) where
  addCtxRev = AddHere ctx
--instance CAddCtxRev 'Z s '[] '[ 'Used s ] where
--  addCtxRev = AddEHere
instance CAddCtxRev x s g g' => CAddCtxRev ('S x) s (u ': g) (u ': g') where
  addCtxRev = AddLater addCtxRev
--instance CAddCtxRev x s '[] g' => CAddCtxRev ('S x) s '[] ('Unused ': g') where
--  addCtxRev = AddELater addCtxRev

class CAddPat p t g g' | p t g -> g' where
  addPat :: AddPat p t g g'



-- Singleton Context ------------------------------------------

class CSingletonCtx x s g | x s -> g where
  singletonCtx :: SingletonCtx x s g

instance CSingletonCtx 'Z s '[ 'Used s ] where
  singletonCtx = AddHereS 
instance CSingletonCtx x s g 
      => CSingletonCtx ('S x) s ('Unused ': g) where
  singletonCtx = AddLaterS singletonCtx

-- Merge ----------------------------------------------------

class CMerge g1 g2 g3 | g1 g2 -> g3 where
  merge :: Merge g1 g2 g3

instance CMerge '[] '[] '[] where
  merge = MergeE
instance CMerge '[] (u ': g) (u ': g) where
  merge = MergeEL
instance CMerge (u ': g) '[] (u ': g) where
  merge = MergeER
instance CMerge g1 g2 g3 
      => CMerge ('Used t ': g1) ('Unused ': g2) ('Used t ': g3) where
  merge = MergeL merge
instance CMerge g1 g2 g3 
      => CMerge ('Unused ': g1) ('Used t ': g2) ('Used t ': g3) where
  merge = MergeR merge
instance CMerge g1 g2 g3 
      => CMerge ('Unused ': g1) ('Unused ': g2) ('Unused ': g3) where
  merge = MergeU merge

class CMerge2 g1 g2 g3 | g1 g3 -> g2 where
  merge2 :: Merge g1 g2 g3

instance CMerge2 '[] '[] '[] where
  merge2 = MergeE
instance CMerge2 '[] (u ': g) (u ': g) where
  merge2 = MergeEL
instance CMerge2 g1 g2 g3 
      => CMerge2 ('Used t ': g1) ('Unused ': g2) ('Used t ': g3) where
  merge2 = MergeL merge2
instance CMerge2 g1 g2 g3 
      => CMerge2 ('Unused ': g1) ('Used t ': g2) ('Used t ': g3) where
  merge2 = MergeR merge2
instance CMerge2 g1 g2 g3 
      => CMerge2 ('Unused ': g1) ('Unused ': g2) ('Unused ': g3) where
  merge2 = MergeU merge2
