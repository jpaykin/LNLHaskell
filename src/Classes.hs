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

class CIn x s g where
  inCtx :: In x s g

instance CIn 'Z s ('End s) where
  inCtx = InEnd
instance KnownNCtx g => CIn 'Z s ('Cons ('Used s) g) where
  inCtx = InHere nctx
instance CIn x s g => CIn ('S x) s ('Cons u g) where
  inCtx = InLater inCtx

-- Add To Context ----------------------------------------------

class CAddCtx x s g g' | x s g -> g' where
  addCtx :: AddCtx x s g g'
class CAddCtxN x s g g' | x s g -> g' where
  addCtxN :: AddCtxN x s g g'

instance CAddCtxN 'Z s 'Empty ('End s) where
  addCtxN = AddEHere
instance CAddCtxN 'Z s ('N ('Cons 'Unused g)) ('Cons ('Used s) g) where
  addCtxN = AddHere
instance CAddCtxN x s 'Empty g => CAddCtxN ('S x) s 'Empty ('Cons 'Unused g) where
  addCtxN = AddELater addCtxN
instance CAddCtxN x s ('N g) g' => CAddCtxN ('S x) s ('N ('Cons u g)) ('Cons u g') where
  addCtxN = AddLater addCtxN

instance CAddCtxN x s g g' => CAddCtx x s g ('N g') where
  addCtx = AddN $ addCtxN


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
