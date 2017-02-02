{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Classes where

import Data.Constraint
import Prelude hiding (div)

import Prelim
import Context
import Proofs

-- Singleton instance

class KnownUsage u where
  usg :: SUsage Phantom u

instance KnownUsage 'Unused where
  usg = SUnused
instance KnownUsage ('Used σ) where
  usg = SUsed @_ @_ @σ Phantom

class KnownCtx g where
  ctx :: SCtx Phantom g
class KnownNCtx g where
  nctx :: SNCtx Phantom g

instance KnownCtx 'Empty where
  ctx = SEmpty
instance KnownNCtx g => KnownCtx ('N g) where
  ctx = SN nctx

instance KnownNCtx ('End τ) where
  nctx = SEnd Phantom
instance (KnownUsage u, KnownNCtx g) => KnownNCtx ('Cons u g) where
  nctx = SCons usg nctx


-- In Context ---------------------------------------------

class CInN x σ g where
  inNCtx :: InN x σ g

instance CInN 'Z σ ('End σ) where
  inNCtx = InEnd
instance KnownNCtx g => CInN 'Z σ ('Cons ('Used σ) g) where
  inNCtx = InHere nctx
instance (KnownUsage u, CInN x σ g) => CInN ('S x) σ ('Cons u g) where
  inNCtx = InLater usg inNCtx

class CIn x σ g where
  inCtx :: In x σ g

instance CInN x σ g => CIn x σ ('N g) where
  inCtx = In inNCtx
  

-- Add To Context ----------------------------------------------

class CAddCtx x σ g g' | x σ g -> g', x g' -> σ g where
  addCtx :: AddCtx x σ g g'

instance CAddCtxN x σ g g' (IsSingleton g') => CAddCtx x σ g ('N g') where
  addCtx = AddN $ addCtxN @x @σ @g @g' @(IsSingleton g')

-- If CAddCtxN x σ g g' flag then 
-- flag IFF g' is a singleton context IFF g is the empty context
class CAddCtxN x σ g g' flag | x σ g -> g' flag, x g' flag -> σ g where
  addCtxN :: AddCtxN x σ g g'

instance CSingletonNCtx x σ g' => CAddCtxN x σ 'Empty g' 'True  where
  addCtxN = AddS singletonNCtx
instance CAddNCtxN x σ g g' => CAddCtxN x σ ('N g) g' 'False where
  addCtxN = AddNN addNCtxN

class CAddNCtxN x σ g g' | x σ g -> g', x g' -> σ g where
  addNCtxN :: AddNCtxN x σ g g'

instance CAddNCtxFlag x σ g g' (IsDouble g') => CAddNCtxN x σ g g' where
  addNCtxN = addNCtxFlag

-- If CAddNCtxFlag x σ g g' flag then
-- flag IFF g is a singleton context iff g' is a double context
class CAddNCtxFlag x σ g g' flag | x σ g -> g' flag, x g' flag -> σ g where
  addNCtxFlag :: AddNCtxN x σ g g'

instance (KnownNCtx g, IsSingleton g ~ flag)
    => CAddNCtxFlag 'Z σ ('Cons 'Unused g) ('Cons ('Used σ) g) flag where
  addNCtxFlag = AddHere nctx
instance CSingletonNCtx x σ g => CAddNCtxFlag ('S x) σ ('End τ) ('Cons ('Used τ) g) 'True where
  addNCtxFlag = AddEnd singletonNCtx
instance CAddNCtxFlag x σ g g' f => CAddNCtxFlag ('S x) σ ('Cons 'Unused g) ('Cons 'Unused g') f where
  addNCtxFlag = AddLater SUnused addNCtxFlag
instance CAddNCtxN x σ g g' => CAddNCtxFlag ('S x) σ ('Cons ('Used τ) g) ('Cons ('Used τ) g') 'False where
  addNCtxFlag = AddLater (SUsed Phantom) addNCtxN


---------------------

-- outputs the number of variables used in the NCtx
type family CountN g :: Nat where
  CountN ('End _)            = 'S 'Z
  CountN ('Cons ('Used _) g) = 'S (CountN g)
  CountN ('Cons 'Unused g)   = CountN g

type family IsSingleton  g :: Bool where
  IsSingleton ('End σ)            = 'True
  IsSingleton ('Cons ('Used _) _) = 'False
  IsSingleton ('Cons 'Unused   g) = IsSingleton g

type family IsDouble g :: Bool where
  IsDouble ('End σ) = 'False
  IsDouble ('Cons ('Used _) g) = IsSingleton g
  IsDouble ('Cons 'Unused g)   = IsDouble g

class CIsSingleton g flag | g -> flag where
  isSingleton :: Dict (IsSingleton g ~ flag)

instance CIsSingleton ('End σ) 'True where
  isSingleton = Dict
instance CIsSingleton ('Cons ('Used σ) g) 'False where
  isSingleton = Dict
instance CIsSingleton g b => CIsSingleton ('Cons 'Unused g) b where
  isSingleton = case isSingleton @g of Dict -> Dict

-- Singleton Context ------------------------------------------

class CSingletonCtx x σ g | x σ -> g, g -> x σ where
  singletonCtx :: SingletonCtx x σ g
class CSingletonNCtx x σ g | x σ -> g, g -> x σ where
  singletonNCtx :: SingletonNCtx x σ g

instance CSingletonNCtx 'Z σ ('End σ) where
  singletonNCtx = AddHereS
instance CSingletonNCtx x σ g => CSingletonNCtx ('S x) σ ('Cons 'Unused g) where
  singletonNCtx = AddLaterS singletonNCtx

instance CSingletonNCtx x σ g => CSingletonCtx x σ ('N g) where
  singletonCtx = SingN $ singletonNCtx


-- Remove Context ------------------------------------------

class CRemoveCtx x σ g g' | x σ g -> g', x σ g' -> g where
  removeCtx :: AddCtx x σ g' g

instance CAddCtx x σ g' g => CRemoveCtx x σ g g' where
  removeCtx = addCtx


-- Merge ----------------------------------------------------


class CMergeU u1 u2 u3 | u1 u2 -> u3, u1 u3 -> u2, u2 u3 -> u1 where
  mergeU :: MergeU u1 u2 u3

instance CMergeU 'Unused 'Unused 'Unused where
  mergeU = MergeUn
instance CMergeU ('Used σ) 'Unused ('Used σ) where
  mergeU = MergeUL
instance CMergeU 'Unused ('Used σ) ('Used σ) where
  mergeU = MergeUR

class (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2) => CMerge g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1 where
  merge :: Merge g1 g2 g3

instance (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2) => CMerge g1 g2 g3 where
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

instance KnownNCtx g2 => CMergeNForward ('End σ) ('Cons 'Unused g2) ('Cons ('Used σ) g2) where
  mergeNF = MergeEndL nctx
instance KnownNCtx g1 => CMergeNForward ('Cons 'Unused g1) ('End σ) ('Cons ('Used σ) g1) where
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

instance σ ~ τ => CDivN ('End σ) ('End τ) 'Empty where
  divN = DivEndEnd
instance KnownNCtx g => CDivN ('Cons ('Used σ) g) ('End σ) ('N ('Cons 'Unused g)) where
  divN = DivConsEnd nctx
instance (CMergeU u3 u2 u1, CDivN g1 g2 g3, g3' ~ ConsN u3 g3)
      => CDivN ('Cons u1 g1) ('Cons u2 g2) g3' where
  divN = DivConsCons divN mergeU


