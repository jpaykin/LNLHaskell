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

class CAddCtx x s g g' | x s g -> g', x g' -> s g where
  addCtx :: AddCtx x s g g'

instance CAddCtxN x s g g' (IsSingleton g') => CAddCtx x s g ('N g') where
  addCtx = AddN $ addCtxN @x @s @g @g' @(IsSingleton g')

class CAddCtxN x s g g' flag | x s g -> g' flag, x g' flag -> s g where
  addCtxN :: AddCtxN x s g g'

instance CSingletonNCtx x s g' => CAddCtxN x s 'Empty g' 'True  where
  addCtxN = AddS singletonNCtx
instance CAddNCtxN x s g g' => CAddCtxN x s ('N g) g' 'False where
  addCtxN = AddNN addNCtxN

class CAddNCtxN x s g g' | x s g -> g', x g' -> s g where
  addNCtxN :: AddNCtxN x s g g'

instance CAddNCtxFlag x s g g' (IsDouble g') => CAddNCtxN x s g g' where
  addNCtxN = addNCtxFlag

class CAddNCtxFlag x s g g' flag | x s g -> g' flag, x g' flag -> s g where
  addNCtxFlag :: AddNCtxN x s g g'

instance (KnownNCtx g, IsSingleton g ~ flag)
    => CAddNCtxFlag 'Z s ('Cons 'Unused g) ('Cons ('Used s) g) flag where
  addNCtxFlag = AddHere nctx
instance CSingletonNCtx x s g => CAddNCtxFlag ('S x) s ('End t) ('Cons ('Used t) g) 'True where
  addNCtxFlag = AddEnd singletonNCtx
instance CAddNCtxFlag x s g g' 'True => CAddNCtxFlag ('S x) s ('Cons 'Unused g) ('Cons 'Unused g') 'True where
  addNCtxFlag = AddLater SUnused addNCtxFlag
instance CAddNCtxN x s g g' => CAddNCtxFlag ('S x) s ('Cons ('Used t) g) ('Cons ('Used t) g') 'False where
  addNCtxFlag = AddLater SUsed addNCtxN




---------------------

-- outputs the number of variables used in the NCtx
type family CountN g :: Nat where
  CountN ('End _)            = 'S 'Z
  CountN ('Cons ('Used _) g) = 'S (CountN g)
  CountN ('Cons 'Unused g)   = CountN g

type family IsSingleton  g :: Bool where
  IsSingleton ('End s)            = 'True
  IsSingleton ('Cons ('Used _) _) = 'False
  IsSingleton ('Cons 'Unused   g) = IsSingleton g

type family IsDouble g :: Bool where
  IsDouble ('End s) = 'False
  IsDouble ('Cons ('Used _) g) = IsSingleton g
  IsDouble ('Cons 'Unused g)   = IsDouble g

class CIsSingleton g flag | g -> flag where
  isSingleton :: Dict (IsSingleton g ~ flag)

instance CIsSingleton ('End s) 'True where
  isSingleton = Dict
instance CIsSingleton ('Cons ('Used s) g) 'False where
  isSingleton = Dict
instance CIsSingleton g b => CIsSingleton ('Cons 'Unused g) b where
  isSingleton = case isSingleton @g of Dict -> Dict

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
  removeCtx :: AddCtx x s g' g

instance CAddCtx x s g' g => CRemoveCtx x s g g' where
  removeCtx = addCtx


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
instance KnownNCtx g => CMergeForward 'Empty ('N g) ('N g) where
  mergeF = MergeEL nctx
instance KnownNCtx g => CMergeForward ('N g) 'Empty ('N g) where
  mergeF = MergeER nctx
instance CMergeNForward g1 g2 g3 => CMergeForward ('N g1) ('N g2) ('N g3) where
  mergeF = MergeN mergeNF

instance KnownNCtx g2 => CMergeNForward ('End s) ('Cons 'Unused g2) ('Cons ('Used s) g2) where
  mergeNF = MergeEndL nctx
instance KnownNCtx g1 => CMergeNForward ('Cons 'Unused g1) ('End s) ('Cons ('Used s) g1) where
  mergeNF = MergeEndR (nctx @g1)
instance (CMergeU u1 u2 u3, CMergeNForward g1 g2 g3)
      => CMergeNForward ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3) where
  mergeNF = MergeCons mergeU mergeNF


-- Div ---------------------------------------

class CDiv g1 g2 g3 | g1 g2 -> g3 where
  div :: Div g1 g2 g3

instance CDiv 'Empty 'Empty 'Empty where
  div = DivEmpty SEmpty
instance KnownNCtx g => CDiv ('N g) 'Empty ('N g) where
  div = DivEmpty ctx
instance CDivN g1 g2 g3 => CDiv ('N g1) ('N g2) g3 where
  div = DivN divN

class CDivN g1 g2 g3 | g1 g2 -> g3 where
  divN :: DivN g1 g2 g3

instance s ~ t => CDivN ('End s) ('End t) 'Empty where
  divN = DivEndEnd
instance KnownNCtx g => CDivN ('Cons ('Used s) g) ('End s) ('N ('Cons 'Unused g)) where
  divN = DivConsEnd nctx
instance (CMergeU u3 u2 u1, CDivN g1 g2 g3, g3' ~ ConsN u3 g3)
      => CDivN ('Cons u1 g1) ('Cons u2 g2) g3' where
  divN = DivConsCons divN mergeU


