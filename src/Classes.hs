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

-- Singleton instance

class KnownUsage u where
  usg :: SUsage u

instance KnownUsage 'Unused where
  usg = SUnused
instance KnownUsage ('Used s) where
  usg = SUsed @s

class KnownCtx g where
  ctx :: SCtx g
class KnownNCtx g where
  nctx :: SNCtx g

instance KnownCtx 'Empty where
  ctx = SEmpty
instance KnownNCtx g => KnownCtx ('N g) where
  ctx = SN nctx

instance KnownNCtx ('End t) where
  nctx = SEnd
instance (KnownUsage u, KnownNCtx g) => KnownNCtx ('Cons u g) where
  nctx = SCons usg nctx


-- In Context ---------------------------------------------

class CInN x s g where
  inNCtx :: InN x s g

instance CInN 'Z s ('End s) where
  inNCtx = InEnd
instance KnownNCtx g => CInN 'Z s ('Cons ('Used s) g) where
  inNCtx = InHere nctx
instance CInN x s g => CInN ('S x) s ('Cons u g) where
  inNCtx = InLater inNCtx

class CIn x s g where
  inCtx :: In x s g

instance CInN x s g => CIn x s ('N g) where
  inCtx = In inNCtx
  

-- Add To Context ----------------------------------------------

class CAddCtx x s g g' | x s g -> g' where
  addCtx :: AddCtx x s g g'
class CAddCtxN x s g g' | x s g -> g' where
  addCtxN :: AddCtxN x s g g'
class CAddNCtxN x s g g' | x s g -> g' where
  addNCtxN :: AddNCtxN x s g g'

-- to do: add instances

-- Singleton Context ------------------------------------------

class CSingletonCtx x s g | x s -> g where
  singletonCtx :: SingletonCtx x s g
class CSingletonNCtx x s g | x s -> g where
  singletonNCtx :: SingletonNCtx x s g

instance CSingletonNCtx 'Z s ('End s) where
  singletonNCtx = AddHereS
instance CSingletonNCtx x s g => CSingletonNCtx ('S x) s ('Cons 'Unused g) where
  singletonNCtx = AddLaterS singletonNCtx

instance CSingletonNCtx x s g => CSingletonCtx x s ('N g) where
  singletonCtx = SingN $ singletonNCtx


-- Merge ----------------------------------------------------


class CMergeU u1 u2 u3 | u1 u2 -> u3, u1 u3 -> u2, u2 u3 -> u1 where
  mergeU :: MergeU u1 u2 u3

instance CMergeU 'Unused 'Unused 'Unused where
  mergeU = MergeUn
instance CMergeU ('Used s) 'Unused ('Used s) where
  mergeU = MergeUL
instance CMergeU 'Unused ('Used s) ('Used s) where
  mergeU = MergeUR

class CMerge g1 g2 g3 | g1 g2 -> g3 where
  merge :: Merge g1 g2 g3

instance CMerge 'Empty 'Empty 'Empty where
  merge = MergeE
instance CMerge 'Empty ('N g) ('N g) where
  merge = MergeEL
instance CMerge ('N g) 'Empty ('N g) where
  merge = MergeER
instance CMergeN g1 g2 g3 => CMerge ('N g1) ('N g2) ('N g3) where
  merge = MergeN mergeN

-- still can't get the extra functional dependencies :(
class CMergeN g1 g2 g3 | g1 g2 -> g3 where
  mergeN :: MergeN g1 g2 g3

instance CMergeN ('End s) ('Cons 'Unused g2) ('Cons ('Used s) g2) where
  mergeN = MergeEndL
instance CMergeN ('Cons 'Unused g1) ('End s) ('Cons ('Used s) g1) where
  mergeN = MergeEndR
instance (CMergeU u1 u2 u3, CMergeN g1 g2 g3) 
      => CMergeN ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3) where
  mergeN = MergeCons mergeU mergeN
