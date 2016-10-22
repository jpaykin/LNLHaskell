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

-- instance CAddCtx 'Z s ('Unused ': g) ('Used s ': g) where
--   addCtx = AddHere 
instance CAddCtx 'Z s '[] '[ 'Used s ] where
  addCtx = AddEHere
instance CAddCtx x s g g' => CAddCtx ('S x) s (u ': g) (u ': g') where
  addCtx = AddLater addCtx
-- instance CAddCtx x s '[] g' => CAddCtx ('S x) s '[] ('Unused ': g') where
--   addCtx = AddELater addCtx

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
