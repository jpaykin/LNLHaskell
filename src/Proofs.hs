{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Proofs where

import Data.Kind
import Data.Constraint

import Types
import Context

-- SContexts ------------------------------------------------

addSCtx :: AddCtx x s g g' -> (SCtx g, SCtx g')
addSCtx (AddN pfA) = (g,SN g')
  where
    (g,g') = addSCtxN pfA

addSCtxN :: AddCtxN x s g g' -> (SCtx g, SNCtx g')
addSCtxN (AddS pfS)  = (SEmpty, singletonSCtxN pfS)
addSCtxN (AddNN pfA) = (SN g, g') 
  where
    (g,g') = addSNCtxN pfA

addSNCtxN :: AddNCtxN x s g g' -> (SNCtx g, SNCtx g')
addSNCtxN (AddHere g) = (SCons SUnused g, SCons SUsed g)
addSNCtxN (AddEnd pfS) = (SEnd, SCons SUsed $ singletonSCtxN pfS)
addSNCtxN (AddLater u pfA) = (SCons u g, SCons u g') 
  where
    (g,g') = addSNCtxN pfA


inSNCtx :: InN x s g -> SNCtx g
inSNCtx InEnd = SEnd
inSNCtx (InHere g) = SCons SUsed g
inSNCtx (InLater u pfI) = SCons u $ inSNCtx pfI

inSCtx :: In x s g -> SCtx g
inSCtx (In pfI) = SN $ inSNCtx pfI

inSIdent :: In x s g -> SIdent x
inSIdent (In pfI) = inNSIdent pfI

inNSIdent :: InN x s g -> SIdent x
inNSIdent InEnd           = SZ
inNSIdent (InHere _)      = SZ
inNSIdent (InLater _ pfI) = SS $ inNSIdent pfI

inSCtxRemove :: InN x s g ->  SCtx (RemoveN x g)
inSCtxRemove InEnd           = SEmpty
inSCtxRemove (InHere g')      = SN $ SCons SUnused g'
inSCtxRemove (InLater u pfI) = consN u $ inSCtxRemove pfI


sCtxNAddN :: SNCtx g -> AddNCtxN x s g g' -> SNCtx g'
sCtxNAddN (SCons _ g) (AddHere _)      = SCons SUsed g
sCtxNAddN SEnd        (AddEnd pfS)     = SCons SUsed $ singletonSCtxN pfS
sCtxNAddN (SCons u g) (AddLater _ pfA) = SCons u $ sCtxNAddN g pfA

sCtxAddN :: SCtx g -> AddCtxN x s g g' -> SNCtx g'
sCtxAddN SEmpty (AddS pfS)      = singletonSCtxN pfS
-- sCtxAddN g      AddEHere        = SEnd
-- sCtxAddN g      (AddELater pfA) = SCons SUnused $ sCtxAddN g pfA
sCtxAddN (SN g) (AddNN pfA)     = sCtxNAddN g pfA

sCtxAdd :: SCtx g -> AddCtx y t g g' -> SCtx g'
sCtxAdd g (AddN pfA) = SN $ sCtxAddN g pfA


singletonSCtxN :: SingletonNCtx x s g -> SNCtx g
singletonSCtxN AddHereS = SEnd
singletonSCtxN (AddLaterS pfS) = SCons SUnused $ singletonSCtxN pfS

singletonSCtx :: SingletonCtx x s g -> SCtx g
singletonSCtx (SingN pfS) = SN $ singletonSCtxN pfS


addToSIdent :: AddCtx x s g g' -> SIdent x
addToSIdent pfA = inSIdent $ addIn pfA

sCtxSing :: forall s x. SIdent x -> SCtx (Singleton x s)
sCtxSing x = SN $ sNCtxSing @s x

sNCtxSing :: forall s x. SIdent x -> SNCtx (SingletonN x s)
sNCtxSing SZ = SEnd
sNCtxSing (SS x) = SCons SUnused $ sNCtxSing @s x

-- Freshness ---------------------------------------------

knownFresh :: SCtx g -> SIdent (Fresh g)
knownFresh SEmpty = SZ
knownFresh (SN g) = knownFreshN g

knownFreshN :: SNCtx g -> SIdent (FreshN g)
knownFreshN SEnd = SS SZ
knownFreshN (SCons SUnused _) = SZ
knownFreshN (SCons SUsed g)   = SS $ knownFreshN g

knownFresh2 :: SCtx g -> SIdent (Fresh2 g)
knownFresh2 SEmpty = SS SZ
knownFresh2 (SN g) = knownFreshN2 g

knownFreshN2 :: SNCtx g -> SIdent (FreshN2 g)
knownFreshN2 SEnd = SS (SS SZ)
knownFreshN2 (SCons SUnused g) = SS (knownFreshN g)
knownFreshN2 (SCons SUsed   g) = SS $ knownFreshN2 g

freshDisjoint :: SCtx g -> Disjoint (Fresh g) (Fresh2 g)
freshDisjoint SEmpty = DisjointZS
freshDisjoint (SN SEnd) = DisjointSS $ DisjointZS
freshDisjoint (SN (SCons SUnused _)) = DisjointZS
freshDisjoint (SN (SCons SUsed   g)) = DisjointSS $ freshDisjoint (SN g)


-- Disjointness --------------------------------------------

disjointRemove :: Disjoint x y -> In x s g -> In y t g -> In x s (Remove y g)
disjointRemove pfD (In pfI) (In pfI') = disjointRemoveN pfD pfI pfI'

disjointRemoveN :: Disjoint x y -> InN x s g -> InN y t g -> In x s (RemoveN y g)
disjointRemoveN DisjointZS       (InHere g)       (InLater _ pfI)  = 
  case inSCtxRemove pfI of 
    SEmpty -> In $ InEnd
    SN g'  -> In $ InHere g'
disjointRemoveN DisjointSZ       (InLater _ pfI)  (InHere g)     = In $ InLater SUnused pfI
disjointRemoveN (DisjointSS pfD) (InLater u pfI1) (InLater _ pfI2) = 
  case disjointRemoveN pfD pfI1 pfI2 of In pfI -> In (InLater u pfI)

-- this is the only possible case since g != Empty
disjointIn :: In x s g -> AddCtx y t g g' -> Disjoint x y
disjointIn (In pfI) (AddN (AddNN pfA)) = disjointInN pfI pfA

disjointInN :: InN x s g -> AddNCtxN y t g g' -> Disjoint x y
disjointInN InEnd           (AddEnd _)       = DisjointZS
disjointInN (InHere _)      (AddLater _ _)   = DisjointZS
disjointInN (InLater _ _)   (AddHere _)      = DisjointSZ
disjointInN (InLater _ pfI) (AddLater u pfA) = DisjointSS $ disjointInN pfI pfA


-- Add To Context ----------------------------------------------

inNAddN :: InN x s g -> AddNCtxN y t g g' -> InN x s g'
inNAddN InEnd           (AddEnd pfS)     = InHere $ singletonSCtxN pfS
inNAddN (InHere g)      (AddLater _ pfS) = InHere $ sCtxNAddN g pfS
inNAddN (InLater _ pfI) (AddHere _)      = InLater SUsed pfI
inNAddN (InLater u pfI) (AddLater _ pfA) = InLater u $ inNAddN pfI pfA

inAddN :: In x s g -> AddCtxN y t g g' -> InN x s g'
inAddN (In pfI) (AddNN pfA) = inNAddN pfI pfA

inAdd :: In x s g -> AddCtx y t g g' -> In x s g'
inAdd pfI (AddN pfA) = In $ inAddN pfI pfA


inAddRemoveLater :: In x s g -> AddCtx y t g g' -> AddCtx y t (Remove x g) (Remove x g')
inAddRemoveLater pfI (AddN pfA) = inAddRemoveLaterN pfI pfA

inAddRemoveLaterN :: In x s g -> AddCtxN y t g g' -> AddCtx y t (Remove x g) (RemoveN x g')
inAddRemoveLaterN (In pfI) (AddNN pfA) = inNAddRemoveLaterN pfI pfA

inNAddRemoveLaterN :: InN x s g -> AddNCtxN y t g g' -> AddCtx y t (RemoveN x g) (RemoveN x g')
inNAddRemoveLaterN InEnd          (AddEnd pfS)     = AddN . AddS $ AddLaterS pfS
inNAddRemoveLaterN (InHere g)     (AddLater u pfS) = AddN . AddNN . AddLater SUnused $ pfS
inNAddRemoveLaterN (InLater _ pfI)  (AddHere g0)   = addHereConsN (inSCtxRemove pfI)
inNAddRemoveLaterN (InLater _ pfI)(AddLater u pfS) = addCons u $ inNAddRemoveLaterN pfI pfS

singletonAdd :: SingletonCtx x s g -> AddCtx x s 'Empty g
singletonAdd (SingN pfS) = AddN $ AddS pfS

addSingleton :: AddCtx x s 'Empty g -> SingletonCtx x s g
addSingleton (AddN pfA) = SingN $ addNSingleton pfA

addNSingleton :: AddCtxN x s 'Empty g -> SingletonNCtx x s g
addNSingleton (AddS pfS) = pfS
--addNSingleton AddEHere = AddHereS
--addNSingleton (AddELater pfA) = AddLaterS $ addNSingleton pfA


addFresh :: SCtx g -> AddCtx (Fresh g) s g (Add (Fresh g) s g)
addFresh g = addAdd g $ knownFresh g


{-
addFreshN :: SCtx g -> AddCtxN (Fresh g) s g (AddN (Fresh g) s g)
addFreshN SEmpty = case singletonAddEq of Dict -> AddS $ singletonFresh _
addFreshN (SN g) = AddNN $ addNFreshN g

addNFreshN :: SNCtx g -> AddNCtxN (FreshN g) s g (AddNN (FreshN g) s g)
addNFreshN SEnd              = AddEnd $ singletonNFresh $ SZ
addNFreshN (SCons SUnused g) = AddHere g
addNFreshN (SCons SUsed   g) = AddLater SUsed $ addNFreshN g


singletonAddEq :: SCtx g -> Dict (Add x s g ~ Singleton x s)
-}
------------------------------------------------

addAdd :: SCtx g -> SIdent x -> AddCtx x s g (Add x s g)
addAdd SEmpty x = AddN . AddS $ singNSingN x
addAdd (SN g) x = AddN . AddNN $ addNAddN g x

addNAddN :: SNCtx g -> SIdent x -> AddNCtxN x s g (AddNN x s g)
addNAddN SEnd              (SS x) = AddEnd $ singNSingN x
addNAddN (SCons SUnused g) SZ     = AddHere g
addNAddN (SCons u g)       (SS x) = AddLater u $ addNAddN g x

singSing :: SIdent x -> SingletonCtx x s (Singleton x s)
singSing x = SingN $ singNSingN x

singNSingN :: SIdent x -> SingletonNCtx x s (SingletonN x s)
singNSingN SZ     = AddHereS
singNSingN (SS x) = AddLaterS $ singNSingN x

mergeMerge :: SCtx g1 -> SCtx g2 -> Merge g1 g2 (Merge12 g1 g2)
mergeMerge SEmpty SEmpty = MergeE
mergeMerge SEmpty (SN g) = MergeEL g
mergeMerge (SN g) SEmpty = MergeER g
mergeMerge (SN g1) (SN g2) = MergeN $ mergeMergeN g1 g2

mergeMergeN :: SNCtx g1 -> SNCtx g2 -> MergeN g1 g2 (MergeN12 g1 g2)
mergeMergeN SEnd (SCons SUnused g2) = MergeEndL g2
mergeMergeN (SCons SUnused g1) SEnd = MergeEndR g1
mergeMergeN (SCons u1 g1) (SCons u2 g2) = MergeCons (mergeMergeU u1 u2) $ mergeMergeN g1 g2

mergeMergeU :: SUsage u1 -> SUsage u2 -> MergeU u1 u2 (MergeU12 u1 u2)
mergeMergeU SUnused SUnused = MergeUn
mergeMergeU SUsed   SUnused = MergeUL
mergeMergeU SUnused SUsed   = MergeUR


-- Singleton Context ------------------------------------------


singletonMergeAdd :: SingletonCtx x s g1 -> Merge g1 g2 g3 -> AddCtx x s g2 g3
singletonMergeAdd (SingN pfS) pfM = singletonNMergeAdd pfS pfM

singletonNMergeAdd :: SingletonNCtx x s g1 -> Merge ('N g1) g2 g3 -> AddCtx x s g2 g3
singletonNMergeAdd pfS (MergeER _)  = singletonAdd (SingN pfS)
singletonNMergeAdd pfS (MergeN pfM) = AddN . AddNN $ singletonNMergeNAdd pfS pfM

singletonNMergeNAdd :: SingletonNCtx x s g1 -> MergeN g1 g2 g3 -> AddNCtxN x s g2 g3
singletonNMergeNAdd AddHereS        (MergeEndL g)       = AddHere g
singletonNMergeNAdd (AddLaterS pfS) (MergeEndR g)       = AddEnd pfS
singletonNMergeNAdd (AddLaterS pfS) (MergeCons pfU pfM) =
  case mergeUInvL pfU of Dict -> AddLater u2 $ singletonNMergeNAdd pfS pfM
  where
    (u1,u2,u3) = mergeSUsage pfU


-- Merge Usages ----------------------------------------------------

mergeUInvL :: MergeU 'Unused u2 u3 -> Dict (u2 ~ u3)
mergeUInvL MergeUn = Dict
mergeUInvL MergeUR = Dict

-- Remove ------------------------------------------

addRemoveEquiv :: AddCtx x s g g' -> Dict (g ~ Remove x g')
addRemoveEquiv (AddN pfA) = case addRemoveNEquiv pfA of Dict -> Dict

addRemoveNEquiv :: AddCtxN x s g g' -> Dict (g ~ RemoveN x g')
addRemoveNEquiv (AddS pfS) = case singletonRemoveN pfS of Dict -> Dict
--addRemoveNEquiv AddEHere = Dict
--addRemoveNEquiv (AddELater pfA) = case addRemoveNEquiv pfA of Dict -> Dict
addRemoveNEquiv (AddNN pfA) = case addNRemoveNEquiv pfA of Dict -> Dict

addNRemoveNEquiv :: AddNCtxN x s g g' -> Dict ('N g ~ RemoveN x g')
addNRemoveNEquiv (AddHere _)  = Dict
addNRemoveNEquiv (AddEnd pfS) =
  case singletonRemoveN pfS of Dict -> Dict
addNRemoveNEquiv (AddLater _ pfA) = 
  case addNRemoveNEquiv pfA of Dict -> Dict



singletonRemove :: SingletonCtx x s g -> Dict (Remove x g ~ 'Empty)
singletonRemove (SingN pfS) = singletonRemoveN pfS

singletonRemoveN :: SingletonNCtx x s g -> Dict (RemoveN x g ~ 'Empty)
singletonRemoveN AddHereS = Dict
singletonRemoveN (AddLaterS pfS) = case singletonRemoveN pfS of Dict -> Dict


-- In -------------------------------
singletonInN :: SingletonNCtx x s g -> InN x s g
singletonInN AddHereS        = InEnd
singletonInN (AddLaterS pfS) = InLater SUnused $ singletonInN pfS

singletonIn :: SingletonCtx x s g -> In x s g
singletonIn (SingN pfS) = In $ singletonInN pfS

addNInN :: AddNCtxN x s g g' -> InN x s g'
addNInN (AddHere g)    = InHere g
addNInN (AddEnd pfS)   = InLater SUsed $ singletonInN pfS
addNInN (AddLater u pfA) = InLater u $ addNInN pfA

addInN :: AddCtxN x s g g' -> InN x s g'
addInN (AddS pfS) = singletonInN pfS
--addInN AddEHere        = InEnd
--addInN (AddELater pfE) = InLater SUnused $ addInN pfE
addInN (AddNN pfA)     = addNInN pfA

addIn :: AddCtx x s g g' -> In x s g'
addIn (AddN pfA) = In $ addInN pfA


singletonInInv :: In x s g -> SingletonCtx y t g -> Dict ('(x,s)~'(y,t))
singletonInInv (In pfI) (SingN pfS) = singletonInNInv pfI pfS

singletonInNInv :: InN x s g -> SingletonNCtx y t g -> Dict ('(x,s)~'(y,t))
singletonInNInv InEnd AddHereS = Dict
singletonInNInv (InLater _ pfI) (AddLaterS pfS) = 
  case singletonInNInv pfI pfS of Dict -> Dict


inAddRemoveN :: InN x s g -> AddCtxN x s (RemoveN x g) g
inAddRemoveN InEnd           = AddS AddHereS
inAddRemoveN (InHere g)      = AddNN $ AddHere g
inAddRemoveN (InLater u pfI) = addConsN u z $ inAddRemoveN pfI 
  where
    z = inSCtxRemove pfI

inAddRemove :: In x s g -> AddCtx x s (Remove x g) g
inAddRemove (In pfI) = AddN $ inAddRemoveN pfI

addELater :: AddCtxN x s 'Empty g -> AddCtxN ('S x) s 'Empty ('Cons 'Unused g)
addELater (AddS pfS) = AddS $ AddLaterS pfS

addEHere :: AddCtxN 'Z s 'Empty ('End s)
addEHere = AddS AddHereS

addCons :: SUsage u -> AddCtx x s g g' -> AddCtx ('S x) s (ConsN u g) (ConsN u g')
addCons u (AddN pfA) = AddN $ addConsN u g pfA 
  where
    (g,_) = addSCtx (AddN pfA)

addConsN :: SUsage u -> SCtx g -> AddCtxN x s g g' -> AddCtxN ('S x) s (ConsN u g) ('Cons u g')
addConsN SUsed   SEmpty    pfA         = AddNN . AddEnd $ addNSingleton pfA
addConsN SUnused SEmpty    pfA         = addELater pfA
addConsN u       (SN g)    (AddNN pfA) = AddNN $ AddLater u pfA

addHereConsN :: SCtx g -> AddCtx 'Z s (ConsN 'Unused g) (ConsN ('Used s) g)
addHereConsN SEmpty  = AddN $ addEHere
addHereConsN (SN g') = AddN . AddNN $ AddHere g'


-- Relation between In and Merge

mergeSUsage :: MergeU g1 g2 g3 -> (SUsage g1, SUsage g2, SUsage g3)
mergeSUsage MergeUn = (SUnused, SUnused, SUnused)
mergeSUsage MergeUL = (SUsed,   SUnused, SUsed)
mergeSUsage MergeUR = (SUnused, SUsed,   SUsed)

{-
mergeSNCtx :: MergeN g1 g2 g -> SNCtx g -> (SNCtx g1, SNCtx g2)
mergeSNCtx (MergeEndL _)       (SCons SUsed g) = (SEnd, SCons SUnused g)
mergeSNCtx (MergeEndR _)       (SCons SUsed g) = (SCons SUnused g, SEnd)
mergeSNCtx (MergeCons pfU pfM) (SCons _ g) = 
  let (u1,u2,u) = mergeSUsage pfU 
      (g1,g2)   = mergeSNCtx pfM g
  in (SCons u1 g1, SCons u2 g2)
-}

mergeSNCtx :: MergeN g1 g2 g -> (SNCtx g1, SNCtx g2, SNCtx g)
mergeSNCtx (MergeEndL g)       = (SEnd, SCons SUnused g, SCons SUsed g)
mergeSNCtx (MergeEndR g)       = (SCons SUnused g, SEnd, SCons SUsed g)
mergeSNCtx (MergeCons pfU pfM) = case (mergeSUsage pfU, mergeSNCtx pfM) of
    ((u1,u2,u3),(g1,g2,g3)) -> (SCons u1 g1, SCons u2 g2, SCons u3 g3)

mergeSCtx :: Merge g1 g2 g -> (SCtx g1, SCtx g2, SCtx g)
mergeSCtx MergeE       = (SEmpty, SEmpty, SEmpty)
mergeSCtx (MergeEL g)  = (SEmpty, SN g, SN g)
mergeSCtx (MergeER g)  = (SN g, SEmpty, SN g)
mergeSCtx (MergeN pfM) = case mergeSNCtx pfM of
    (g1,g2,g3) -> (SN g1, SN g2, SN g3)


mergeNInSplit :: MergeN g1 g2 g -> InN x s g -> Either (InN x s g1) (InN x s g2)
mergeNInSplit (MergeEndL _)       (InHere _)      = Left  InEnd
mergeNInSplit (MergeEndL _)       (InLater _ pfI) = Right (InLater SUnused pfI)
mergeNInSplit (MergeEndR _)       (InHere _)      = Right InEnd
mergeNInSplit (MergeEndR _)       (InLater _ pfI) = Left  (InLater SUnused pfI)
mergeNInSplit (MergeCons pfU pfM) (InHere g)      = 
  let (g1,g2,_) = mergeSNCtx pfM
  in case pfU of
    MergeUL -> Left  $ InHere g1
    MergeUR -> Right $ InHere g2
mergeNInSplit (MergeCons pfU pfM) (InLater u pfI) =  
  let (u1,u2,u3) = mergeSUsage pfU 
  in case mergeNInSplit pfM pfI of
    Left  pfI1 -> Left  $ InLater u1 pfI1
    Right pfI2 -> Right $ InLater u2 pfI2

mergeInSplit :: Merge g1 g2 g -> In x s g -> Either (In x s g1) (In x s g2)
mergeInSplit (MergeEL _)  pfI      = Right pfI
mergeInSplit (MergeER _)  pfI      = Left  pfI
mergeInSplit (MergeN pfM) (In pfI) = 
  case mergeNInSplit pfM pfI of
    Left  pfI1 -> Left  $ In pfI1
    Right pfI2 -> Right $ In pfI2

mergeNIn1 :: MergeN g1 g2 g3 -> InN x s g1
          -> Merge (RemoveN x g1) ('N g2) (RemoveN x g3)
mergeNIn1 (MergeEndL g)          InEnd            = MergeEL $ SCons SUnused g
mergeNIn1 (MergeEndR _)          (InLater _ pfI1) =
    mergeCons MergeUR $ mergeReflR (inSCtxRemove pfI1)
mergeNIn1 (MergeCons MergeUL pfM) (InHere _)      =
    MergeN $ MergeCons MergeUn pfM
mergeNIn1 (MergeCons pfU pfM)     (InLater _ pfI1) =
    mergeCons pfU $ mergeNIn1 pfM pfI1

mergeNIn2 :: MergeN g1 g2 g3 -> InN x s g2 
          -> Merge ('N g1) (RemoveN x g2) (RemoveN x g3) 
mergeNIn2 (MergeEndL _)           (InLater _ pfI2) = 
    mergeCons MergeUL $ mergeReflL (inSCtxRemove pfI2)
mergeNIn2 (MergeEndR g)           InEnd            = MergeER $ SCons SUnused g
mergeNIn2 (MergeCons MergeUR pfM) (InHere _)       = 
    MergeN $ MergeCons MergeUn pfM
mergeNIn2 (MergeCons pfU pfM)     (InLater _ pfI2) = 
    mergeCons pfU $ mergeNIn2 pfM pfI2

mergeIn1 :: Merge g1 g2 g3 -> In x s g1 -> Merge (Remove x g1) g2 (Remove x g3)
mergeIn1 (MergeER _)  (In pfI1) = mergeReflR $ inSCtxRemove pfI1
mergeIn1 (MergeN pfM) (In pfI1) = mergeNIn1 pfM pfI1

mergeIn2 :: Merge g1 g2 g3 -> In x s g2 -> Merge g1 (Remove x g2) (Remove x g3) 
mergeIn2 (MergeEL _)  (In pfI2) = mergeReflL $ inSCtxRemove pfI2
mergeIn2 (MergeN pfM) (In pfI2) = mergeNIn2 pfM pfI2

mergeEmpty :: Merge g1 g2 'Empty -> Dict (g1 ~ 'Empty, g2 ~ 'Empty)
mergeEmpty MergeE = Dict

mergeReflR :: SCtx g -> Merge g 'Empty g
mergeReflR SEmpty = MergeE
mergeReflR (SN g) = MergeER g

mergeReflL :: SCtx g -> Merge 'Empty g g
mergeReflL SEmpty = MergeE
mergeReflL (SN g) = MergeEL g

mergeUCons :: MergeU u1 u2 u3 -> Merge (ConsN u1 'Empty) (ConsN u2 'Empty) (ConsN u3 'Empty)
mergeUCons MergeUn = MergeE
mergeUCons MergeUL = MergeER SEnd
mergeUCons MergeUR = MergeEL SEnd

mergeUConsL :: MergeU u1 u2 u3 -> SNCtx g -> Merge (ConsN u1 'Empty) ('N ('Cons u2 g)) ('N ('Cons u3 g))
mergeUConsL MergeUn g = MergeEL $ SCons SUnused g
mergeUConsL MergeUL g = MergeN  $ MergeEndL g
mergeUConsL MergeUR g = MergeEL $ SCons SUsed g

mergeUConsR :: MergeU u1 u2 u3 -> SNCtx g -> Merge ('N ('Cons u1 g)) (ConsN u2 'Empty) ('N ('Cons u3 g))
mergeUConsR MergeUn g = MergeER $ SCons SUnused g
mergeUConsR MergeUL g = MergeER $ SCons SUsed   g
mergeUConsR MergeUR g = MergeN  $ MergeEndR g


mergeCons :: MergeU u1 u2 u3 -> Merge g1 g2 g3 -> Merge (ConsN u1 g1) (ConsN u2 g2) (ConsN u3 g3)
mergeCons pfU MergeE  = mergeUCons pfU
mergeCons pfU (MergeEL g) = mergeUConsL pfU g
mergeCons pfU (MergeER g) = mergeUConsR pfU g
mergeCons pfU (MergeN pfM) = MergeN $ MergeCons pfU pfM


-- symmetry of merge


mergeUSymm :: MergeU u1 u2 u3 -> MergeU u2 u1 u3
mergeUSymm MergeUn = MergeUn
mergeUSymm MergeUL = MergeUR
mergeUSymm MergeUR = MergeUL

mergeSymm :: Merge g1 g2 g3 -> Merge g2 g1 g3
mergeSymm MergeE = MergeE
mergeSymm (MergeEL g) = MergeER g
mergeSymm (MergeER g) = MergeEL g
mergeSymm (MergeN pfM) = MergeN $ mergeNSymm pfM

mergeNSymm :: MergeN g1 g2 g3 -> MergeN g2 g1 g3
mergeNSymm (MergeEndL g) = MergeEndR g
mergeNSymm (MergeEndR g) = MergeEndL g
mergeNSymm (MergeCons pfU pfM) = MergeCons (mergeUSymm pfU) (mergeNSymm pfM)

-- Div -------------------------------------------------------

divMerge :: Div g3 g2 g1 -> Merge g1 g2 g3
divMerge (DivEmpty g) = mergeReflR g
divMerge (DivN pfD)   = divNMerge pfD

divNMerge :: DivN g3 g2 g1 -> Merge g1 ('N g2) ('N g3)
divNMerge DivEndEnd = MergeEL SEnd
divNMerge (DivConsEnd g) = MergeN $ MergeEndR g
divNMerge (DivConsCons pfD pfU) = mergeCons pfU $ divNMerge pfD

mergeDiv :: Merge g1 g2 g3 -> Div g3 g2 g1
mergeDiv MergeE       = DivEmpty SEmpty
mergeDiv (MergeEL g)  = divAll (SN g)
mergeDiv (MergeER g)  = DivEmpty (SN g)
mergeDiv (MergeN pfM) = DivN $ mergeNDiv pfM

mergeNDiv :: MergeN g1 g2 g3 -> DivN g3 g2 ('N g1)
mergeNDiv (MergeEndL g)       = DivConsCons (divNAll g) MergeUL
mergeNDiv (MergeEndR g)       = DivConsEnd g
mergeNDiv (MergeCons pfU pfM) = DivConsCons (mergeNDiv pfM) pfU

divAll :: SCtx g -> Div g g 'Empty
divAll SEmpty = DivEmpty SEmpty
divAll (SN g) = DivN $ divNAll g

divNAll :: SNCtx g -> DivN g g 'Empty
divNAll SEnd = DivEndEnd
divNAll (SCons u g) = DivConsCons (divNAll g) (divUAll u)

divUAll :: SUsage u -> MergeU 'Unused u u
divUAll SUsed   = MergeUR
divUAll SUnused = MergeUn
