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

class CAddCtx x s g g' | x s g -> g', x s g' -> g where
  addCtx :: AddCtx x s g g'

instance (CSingletonCtx x s gx, CMerge gx g g') => CAddCtx x s g g' where
  addCtx = singletonMergeAdd (singletonCtx @x @s @gx)  merge


-- class CAddCtxN x s g g' | x s g -> g' where
--   addCtxN :: AddCtxN x s g g'
-- class CAddNCtxN x s g g' | x s g -> g', x g' -> s g where
--   addNCtxN :: AddNCtxN x s g g'

--instance KnownNCtx g => CAddNCtxN 'Z s ('Cons 'Unused g) ('Cons ('Used s) g) where
--  addNCtxN = AddHere nctx

-- instance CSingletonNCtx x s g => CAddNCtxN ('S x) s ('End t) ('Cons ('Used t) g) where
--   addNCtxN = AddEnd singletonNCtx
-- instance (KnownUsage u, CAddNCtxN x s g g') => CAddNCtxN ('S x) s ('Cons u g) ('Cons u g') where
--   addNCtxN = AddLater usg addNCtxN

-- instance CAddCtxN 'Z s 'Empty ('End s) where
--   addCtxN = AddEHere
-- instance CAddCtxN x s 'Empty g => CAddCtxN ('S x) s 'Empty ('Cons 'Unused g) where
--   addCtxN = AddELater addCtxN
-- instance CAddNCtxN x s g g' => CAddCtxN x s ('N g) g' where
--   addCtxN = AddNN addNCtxN

-- instance CAddCtxN x s g g' => CAddCtx x s g ('N g') where
--   addCtx = AddN addCtxN

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


-- Remove Context ------------------------------------------

class CRemoveCtx x s g g' | x s g -> g', x s g' -> g where
  removeCtx :: RemoveCtx x s g g'

instance CAddCtx x s g' g => CRemoveCtx x s g g' where
  removeCtx = addRemove addCtx


-- Shift ----------------------------------------------------

class CShiftCtx u g g' | u g -> g', u g' -> g where
  shiftCtx :: ShiftCtx u g g'

instance CShiftCtx ('Used s) 'Empty ('N ('End s)) where
  shiftCtx = ShiftEmptyUsed
instance CShiftCtx 'Unused 'Empty 'Empty where
  shiftCtx = ShiftEmptyUnused
instance CShiftCtx u ('N g) ('N ('Cons u g)) where
  shiftCtx = ShiftN

-- Merge ----------------------------------------------------


class CMergeU u1 u2 u3 | u1 u2 -> u3, u1 u3 -> u2, u2 u3 -> u1 where
  mergeU :: MergeU u1 u2 u3

instance CMergeU 'Unused 'Unused 'Unused where
  mergeU = MergeUn
instance CMergeU ('Used s) 'Unused ('Used s) where
  mergeU = MergeUL
instance CMergeU 'Unused ('Used s) ('Used s) where
  mergeU = MergeUR

class CMerge g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1 where
  merge :: Merge g1 g2 g3

instance (CMergeForward g1 g2 g3, CDiv g3 g2 g1, CDiv g3 g1 g2) => CMerge g1 g2 g3 where
  merge = divMerge div

class CMergeForward g1 g2 g3 | g1 g2 -> g3 where
  mergeF :: Merge g1 g2 g3
class CMergeNForward g1 g2 g3 | g1 g2 -> g3 where
  mergeNF :: MergeN g1 g2 g3

instance CMergeForward 'Empty 'Empty 'Empty where
  mergeF = MergeE
instance CMergeForward 'Empty ('N g) ('N g) where
  mergeF = MergeEL
instance CMergeForward ('N g) 'Empty ('N g) where
  mergeF = MergeER
instance CMergeNForward g1 g2 g3 => CMergeForward ('N g1) ('N g2) ('N g3) where
  mergeF = MergeN mergeNF

instance CMergeNForward ('End s) ('Cons 'Unused g2) ('Cons ('Used s) g2) where
  mergeNF = MergeEndL
instance CMergeNForward ('Cons 'Unused g1) ('End s) ('Cons ('Used s) g1) where
  mergeNF = MergeEndR
instance (CMergeU u1 u2 u3, CMergeNForward g1 g2 g3)
      => CMergeNForward ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3) where
  mergeNF = MergeCons mergeU mergeNF


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


