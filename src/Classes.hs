{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Classes where

import Data.Kind
import Data.Constraint
import Prelude hiding (div)

import Types
import Context
import Proofs

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
instance (KnownUsage u, CInN x s g) => CInN ('S x) s ('Cons u g) where
  inNCtx = InLater usg inNCtx

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

instance KnownNCtx g => CAddNCtxN 'Z s ('Cons 'Unused g) ('Cons ('Used s) g) where
  addNCtxN = AddHere nctx
-- instance CAddCtxN x s 'Empty g => CAddNCtxN ('S x) s ('End t) ('Cons ('Used t) g) where
--   addNCtxN = AddEnd $ addNSingleton addCtxN
-- instance (KnownUsage u, CAddCtxN x s ('N g) g') 
--       => CAddNCtxN ('S x) s ('Cons u g) ('Cons u g') where
--   addNCtxN = case addCtxN @x @s @('N g) @g' of AddNN pfA -> AddLater usg pfA

instance CSingletonNCtx x s g => CAddNCtxN ('S x) s ('End t) ('Cons ('Used t) g) where
  addNCtxN = AddEnd singletonNCtx
instance (KnownUsage u, CAddNCtxN x s g g') => CAddNCtxN ('S x) s ('Cons u g) ('Cons u g') where
  addNCtxN = AddLater usg addNCtxN
  

instance CAddCtxN 'Z s 'Empty ('End s) where
  addCtxN = AddEHere
instance CAddCtxN x s 'Empty g => CAddCtxN ('S x) s 'Empty ('Cons 'Unused g) where
  addCtxN = AddELater addCtxN
instance CAddNCtxN x s g g' => CAddCtxN x s ('N g) g' where
  addCtxN = AddNN addNCtxN

instance CAddCtxN x s g g' => CAddCtx x s g ('N g') where
  addCtx = AddN addCtxN

-- Singleton Context ------------------------------------------

class CSingletonCtx x s g | x s -> g, g -> x s where
  singletonCtx :: SingletonCtx x s g
class CSingletonNCtx x s g | x s -> g, g -> x s where
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

class CMerge g1 g2 g3 | g1 g3 -> g2, g2 g3 -> g1 where
  merge :: Merge g1 g2 g3

instance (CDiv g3 g2 g1, CDiv g3 g1 g2) => CMerge g1 g2 g3 where
  merge = divMerge div
  

-- Div ---------------------------------------

class CDiv g1 g2 g3 | g1 g2 -> g3 where
  div :: Div g1 g2 g3

instance CDiv g 'Empty g where
  div = DivEmpty
instance CDivN g1 g2 g3 => CDiv ('N g1) ('N g2) g3 where
  div = DivN divN

class CDivN g1 g2 g3 | g1 g2 -> g3 where
  divN :: DivN g1 g2 g3

instance CDivN ('End s) ('End s) 'Empty where
  divN = DivEndEnd
instance CDivN ('Cons ('Used s) g') ('End s) ('N ('Cons 'Unused g')) where
  divN = DivConsEnd
instance (CMergeU u3 u2 u1, CDivN g1 g2 g3, g3' ~ ConsN u3 g3)
      => CDivN ('Cons u1 g1) ('Cons u2 g2) g3' where
  divN = DivConsCons divN mergeU


