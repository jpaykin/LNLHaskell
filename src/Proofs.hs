{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Proofs where

import Prelim
import Context

-- Singleton Nats and Contexts ------------------------------------------------

-- Extract the Singleton Nat from a proof that the nat is in a context
inSNat :: In x s g -> SNat x
inSNat (In pfI) = inNSNat pfI

inNSNat :: InN x s g -> SNat x
inNSNat InEnd           = SZ
inNSNat (InHere _)      = SZ
inNSNat (InLater _ pfI) = SS $ inNSNat pfI

addToSNat :: AddCtx x s g g' -> SNat x
addToSNat pfA = inSNat $ addIn pfA

-- Given a usage and a context, construct the singleton context for (u:g)
consN :: SUsage d u -> SCtx d g -> SCtx d (ConsN u g) 
consN (SUsed d) SEmpty = SN $ SEnd d
consN SUnused   SEmpty = SEmpty
consN u         (SN g) = SN $ SCons u g

-- Given a proof that g1,g2=g, obtain the singleton contexts for each of g1, g2,
-- and g.
mergeSCtx :: Merge g1 g2 g -> (SCtx Phantom g1, SCtx Phantom g2, SCtx Phantom g)
mergeSCtx MergeE       = (SEmpty, SEmpty, SEmpty)
mergeSCtx (MergeEL g)  = (SEmpty, SN g, SN g)
mergeSCtx (MergeER g)  = (SN g, SEmpty, SN g)
mergeSCtx (MergeN pfM) = case mergeSNCtx pfM of
    (g1,g2,g3) -> (SN g1, SN g2, SN g3)

mergeSUsage :: MergeU g1 g2 g3 -> (SUsage Phantom g1, SUsage Phantom g2, SUsage Phantom g3)
mergeSUsage MergeUn = (SUnused,       SUnused,       SUnused)
mergeSUsage MergeUL = (SUsed Phantom, SUnused,       SUsed Phantom)
mergeSUsage MergeUR = (SUnused,       SUsed Phantom, SUsed Phantom)

mergeSNCtx :: MergeN g1 g2 g -> (SNCtx Phantom g1, SNCtx Phantom g2, SNCtx Phantom g)
mergeSNCtx (MergeEndL g)       = (SEnd Phantom, SCons SUnused g, SCons (SUsed Phantom) g)
mergeSNCtx (MergeEndR g)       = (SCons SUnused g, SEnd Phantom, SCons (SUsed Phantom) g)
mergeSNCtx (MergeCons pfU pfM) = case (mergeSUsage pfU, mergeSNCtx pfM) of
    ((u1,u2,u3),(g1,g2,g3)) -> (SCons u1 g1, SCons u2 g2, SCons u3 g3)


-- Freshness ---------------------------------------------

-- Constructs a fresh Nat that does not occur in the context g
knownFresh :: SCtx d g -> SNat (Fresh g)
knownFresh SEmpty = SZ
knownFresh (SN g) = knownFreshN g

knownFreshN :: SNCtx d g -> SNat (FreshN g)
knownFreshN (SEnd _)            = SS SZ
knownFreshN (SCons SUnused _)   = SZ
knownFreshN (SCons (SUsed _) g) = SS $ knownFreshN g

knownFresh2 :: SCtx d g -> SNat (Fresh2 g)
knownFresh2 SEmpty = SS SZ
knownFresh2 (SN g) = knownFreshN2 g

knownFreshN2 :: SNCtx d g -> SNat (FreshN2 g)
knownFreshN2 (SEnd _)            = SS (SS SZ)
knownFreshN2 (SCons SUnused g)   = SS (knownFreshN g)
knownFreshN2 (SCons (SUsed _) g) = SS $ knownFreshN2 g


-- Singleton Context ----------------------------------------------

-- Constructs the canonical proof that (Singleton x s) is a singleton context.
singSing :: SNat x -> SingletonCtx x s (Singleton x s)
singSing x = SingN $ singNSingN x

singNSingN :: SNat x -> SingletonNCtx x s (SingletonN x s)
singNSingN SZ     = AddHereS
singNSingN (SS x) = AddLaterS $ singNSingN x

-- In -------------------------------

-- The variable x is in the singleton ctx (x:s)
singletonIn :: SingletonCtx x s g -> In x s g
singletonIn (SingN pfS) = In $ singletonInN pfS

singletonInN :: SingletonNCtx x s g -> InN x s g
singletonInN AddHereS        = InEnd
singletonInN (AddLaterS pfS) = InLater SUnused $ singletonInN pfS

-- The variable x is in the context g[x↦s]
addIn :: AddCtx x s g g' -> In x s g'
addIn (AddN pfA) = In $ addInN pfA

addInN :: AddCtxN x s g g' -> InN x s g'
addInN (AddS pfS) = singletonInN pfS
addInN (AddNN pfA)     = addNInN pfA

addNInN :: AddNCtxN x s g g' -> InN x s g'
addNInN (AddHere g)    = InHere g
addNInN (AddEnd pfS)   = InLater (SUsed Phantom) $ singletonInN pfS
addNInN (AddLater u pfA) = InLater u $ addNInN pfA


-- Relation between In and Merge


mergeReflR :: SCtx Phantom g -> Merge g 'Empty g
mergeReflR SEmpty = MergeE
mergeReflR (SN g) = MergeER g

mergeReflL :: SCtx Phantom g -> Merge 'Empty g g
mergeReflL SEmpty = MergeE
mergeReflL (SN g) = MergeEL g

mergeUCons :: MergeU u1 u2 u3 -> Merge (ConsN u1 'Empty) (ConsN u2 'Empty) (ConsN u3 'Empty)
mergeUCons MergeUn = MergeE
mergeUCons MergeUL = MergeER $ SEnd Phantom
mergeUCons MergeUR = MergeEL $ SEnd Phantom

mergeUConsL :: MergeU u1 u2 u3 -> SNCtx Phantom g 
            -> Merge (ConsN u1 'Empty) ('N ('Cons u2 g)) ('N ('Cons u3 g))
mergeUConsL MergeUn g = MergeEL $ SCons SUnused g
mergeUConsL MergeUL g = MergeN  $ MergeEndL g
mergeUConsL MergeUR g = MergeEL $ SCons (SUsed Phantom) g

mergeUConsR :: MergeU u1 u2 u3 -> SNCtx Phantom g 
            -> Merge ('N ('Cons u1 g)) (ConsN u2 'Empty) ('N ('Cons u3 g))
mergeUConsR MergeUn g = MergeER $ SCons SUnused g
mergeUConsR MergeUL g = MergeER $ SCons (SUsed Phantom) g
mergeUConsR MergeUR g = MergeN  $ MergeEndR g


mergeCons :: MergeU u1 u2 u3 -> Merge g1 g2 g3 -> Merge (ConsN u1 g1) (ConsN u2 g2) (ConsN u3 g3)
mergeCons pfU MergeE  = mergeUCons pfU
mergeCons pfU (MergeEL g) = mergeUConsL pfU g
mergeCons pfU (MergeER g) = mergeUConsR pfU g
mergeCons pfU (MergeN pfM) = MergeN $ MergeCons pfU pfM

-- Div -------------------------------------------------------

divMerge :: Div g3 g2 g1 -> Merge g1 g2 g3
divMerge (DivEmpty g) = mergeReflR g
divMerge (DivN pfD)   = divNMerge pfD

divNMerge :: DivN g3 g2 g1 -> Merge g1 ('N g2) ('N g3)
divNMerge DivEndEnd = MergeEL $ SEnd Phantom
divNMerge (DivConsEnd g) = MergeN $ MergeEndR g
divNMerge (DivConsCons pfD pfU) = mergeCons pfU $ divNMerge pfD

-- SCtxs with non-phantom data ----------------------------------

lookup :: In x s g -> SCtx dat g -> dat s
lookup (In pfI) (SN g) = lookupN pfI g

lookupN :: InN x s g -> SNCtx dat g -> dat s
lookupN InEnd           (SEnd v)            = v
lookupN (InHere _)      (SCons (SUsed v) _) = v
lookupN (InLater _ pfI) (SCons _ g)         = lookupN pfI g

splitSCtx :: Merge g1 g2 g -> SCtx dat g -> (SCtx dat g1, SCtx dat g2)
splitSCtx MergeE SEmpty = (SEmpty, SEmpty)
splitSCtx (MergeEL _) g = (SEmpty, g)
splitSCtx (MergeER _) g = (g, SEmpty)
splitSCtx (MergeN pfM) (SN g) = (SN g1, SN g2) 
  where
    (g1,g2) = splitSNCtx pfM g

splitSNCtx :: MergeN g1 g2 g -> SNCtx dat g -> (SNCtx dat g1, SNCtx dat g2)
splitSNCtx (MergeEndL _) (SCons (SUsed v) g2) = (SEnd v, SCons SUnused g2)
splitSNCtx (MergeEndR _) (SCons (SUsed v) g1) = (SCons SUnused g1, SEnd v)
splitSNCtx (MergeCons pfU pfM) (SCons u g) = (SCons u1 g1, SCons u2 g2)
  where
    (u1,u2) = splitSUsage pfU u
    (g1,g2) = splitSNCtx pfM g

splitSUsage :: MergeU u1 u2 u -> SUsage dat u -> (SUsage dat u1, SUsage dat u2)
splitSUsage MergeUn SUnused = (SUnused, SUnused)
splitSUsage MergeUL u       = (u,SUnused)
splitSUsage MergeUR u       = (SUnused, u)

addSCtx :: AddCtx x s g g' -> SCtx dat g -> dat s -> SCtx dat g'
addSCtx (AddN pfA) g v = SN $ addSCtxN pfA g v

addSCtxN :: AddCtxN x s g g' -> SCtx dat g -> dat s -> SNCtx dat g'
addSCtxN (AddS pfS) _ v = singletonSNCtx pfS v
addSCtxN (AddNN pfA) (SN g) v = addSNCtxN pfA g v

addSNCtxN :: AddNCtxN x s g g' -> SNCtx dat g -> dat s -> SNCtx dat g'
addSNCtxN (AddHere _) (SCons SUnused g) v = SCons (SUsed v) g
addSNCtxN (AddEnd pfS) (SEnd v') v = SCons (SUsed v') $ singletonSNCtx pfS v
addSNCtxN (AddLater _ pfA) (SCons u g) v = SCons u $ addSNCtxN pfA g v

singletonSNCtx :: SingletonNCtx x s g -> dat s -> SNCtx dat g
singletonSNCtx AddHereS        v = SEnd v
singletonSNCtx (AddLaterS pfS) v = SCons SUnused $ singletonSNCtx pfS v
