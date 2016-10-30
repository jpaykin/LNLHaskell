{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, DeriveLift, StandaloneDeriving
#-}

module Proofs where

import Data.Kind
import Data.Constraint
import Language.Haskell.TH.Syntax

import Types
import Context

-- singleton types ----------------------------------------------

inSCtxRemove :: forall x s g. In x s g -> SCtx g -> SCtx (Remove x g)
inSCtxRemove (InHere g)    _           = SCons SUnused g
inSCtxRemove (InLater pfI) (SCons u g) = SCons u $ inSCtxRemove pfI g

addToNatS :: AddCtx x s g g' -> NatS x
addToNatS AddEHere        = ZS
addToNatS (AddHere _)     = ZS
addToNatS (AddELater pfA) = SS $ addToNatS pfA
addToNatS (AddLater pfA)  = SS $ addToNatS pfA

addSCtx :: forall y t g g'. 
           AddCtx y t g g'
        -> SCtx g
        -> SCtx g'
addSCtx AddEHere        g = SCons (SUsed @t) g
addSCtx (AddHere g')    _ = SCons (SUsed @t) g'
addSCtx (AddELater pfA) g = SCons SUnused $ addSCtx pfA g
addSCtx (AddLater pfA)  (SCons u g0) = SCons u $ addSCtx pfA g0


sTail :: SCtx (u ': g) -> SCtx g
sTail (SCons u g) = g

-- Shift --------------------------------------------------------

shiftEmpty :: Shift n g1 g2 -> EmptyCtx g1 -> EmptyCtx g2
shiftEmpty ShiftHere            pfEmpty             = EmptyCons pfEmpty  
shiftEmpty (ShiftLater pfShift) (EmptyCons pfEmpty) = EmptyCons (shiftEmpty pfShift pfEmpty)

unshiftEmpty :: Shift n g1 g2 -> EmptyCtx g2 -> EmptyCtx g1
unshiftEmpty ShiftHere            (EmptyCons pfEmpty) = pfEmpty
unshiftEmpty (ShiftLater pfShift) (EmptyCons pfEmpty) = EmptyCons (unshiftEmpty pfShift pfEmpty)

shiftSCtx :: Shift i g g' ->  SCtx g -> SCtx g'
shiftSCtx ShiftHere g = SCons SUnused g
shiftSCtx (ShiftLater pfSh) (SCons u g) = SCons u $ shiftSCtx pfSh g

unshiftSCtx :: Shift i g g' -> SCtx g' -> SCtx g
unshiftSCtx ShiftHere (SCons SUnused g0') = g0'
unshiftSCtx (ShiftLater pfS) (SCons u g0') = SCons u $ unshiftSCtx pfS g0'

-- Equivalent Contexts ------------------------------------------------

equivRefl :: SCtx g -> Equiv g g
equivRefl SNil        = EquivNil
equivRefl (SCons u g) = EquivCons $ equivRefl g

equivSymm :: Equiv g g' -> Equiv g' g
equivSymm EquivNil = EquivNil
equivSymm (EquivEL pf) = EquivER pf
equivSymm (EquivER pf) = EquivEL pf
equivSymm (EquivCons pfE) = EquivCons $ equivSymm pfE

equivTrans :: Equiv g1 g2 -> Equiv g2 g3 -> Equiv g1 g3
equivTrans EquivNil          pfEq = pfEq
equivTrans (EquivEL pfE)     pfEq = EquivEL $ equivEmpty pfE pfEq
equivTrans (EquivER pfE1)    pfEq = emptyEmptyEquiv pfE1 $ equivNilLEmpty pfEq
equivTrans (EquivCons pfEq1) (EquivER (EmptyCons pfE2)) = 
  EquivER $ EmptyCons $ equivEmpty pfE2 $ equivSymm pfEq1
equivTrans (EquivCons pfEq1) (EquivCons pfEq2) = EquivCons $ equivTrans pfEq1 pfEq2

-- if g is equivalent to the empty list, then g is empty
equivNilLEmpty :: Equiv '[] g -> EmptyCtx g
equivNilLEmpty EquivNil      = EmptyNil
equivNilLEmpty (EquivEL pfE) = pfE
equivNilLEmpty (EquivER _)   = EmptyNil

emptyEmptyEquiv :: EmptyCtx g -> EmptyCtx g' -> Equiv g g'
emptyEmptyEquiv EmptyNil EmptyNil = EquivNil
emptyEmptyEquiv EmptyNil pfE      = EquivEL pfE
emptyEmptyEquiv pfE EmptyNil      = EquivER pfE
emptyEmptyEquiv (EmptyCons pfE) (EmptyCons pfE') = EquivCons $ emptyEmptyEquiv pfE pfE'

equivEmpty :: EmptyCtx g -> Equiv g g' -> EmptyCtx g'
equivEmpty EmptyNil        EquivNil         = EmptyNil
equivEmpty EmptyNil        (EquivEL pfE)    = pfE
equivEmpty _               (EquivER _)      = EmptyNil
equivEmpty (EmptyCons pfE) (EquivCons pfEq) = EmptyCons $ equivEmpty pfE pfEq

emptyEquivEmpty :: EmptyCtx g -> EmptyCtx g' -> EquivEmpty g g'
emptyEquivEmpty EmptyNil EmptyNil = EquivENil
emptyEquivEmpty EmptyNil pfE = EquivEEL pfE
emptyEquivEmpty pfE EmptyNil = EquivEER pfE
emptyEquivEmpty (EmptyCons pfE1) (EmptyCons pfE2) = EquivECons $ emptyEquivEmpty pfE1 pfE2

inEquivRemove :: In x s g
              -> Equiv g g'
              -> Equiv (Remove x g) (Remove x g')
inEquivRemove (InHere _)    (EquivCons pfE) = EquivCons pfE
inEquivRemove (InLater pfI) (EquivCons pfE) = EquivCons $ inEquivRemove pfI pfE

inPatEquivRemove :: InPat p t g
            -> Equiv g g'
            -> Equiv (RemovePat p g) (RemovePat p g')
inPatEquivRemove (InVar pfI)    pfE = inEquivRemove pfI pfE
inPatEquivRemove (InTuple pfIs) pfE = inPatsEquivRemove pfIs pfE

inPatsEquivRemove :: InPats ps ts g
                  -> Equiv g g'
                  -> Equiv (RemovePats ps g) (RemovePats ps g')
inPatsEquivRemove (InNil) pfE = pfE
inPatsEquivRemove (InCons pfD pfI pfIs) pfE = inPatEquivRemove pfI' $ inPatsEquivRemove pfIs pfE
  where
 -- pfD :: DisjointPatPats ps' p
 -- pfI :: InPat p t g
 -- pfIs :: InPats ps' ts' g
 -- inPatsEquivRemove pfIs pfE :: Equiv (RemovePats ps' g) (RemovePats ps' g')
 -- pfI' :: InPat p t (RemovePats ps' g)
    pfI' = disjointPatPatsIn pfD pfI pfIs
 -- inPatEquivRemove pfI' ^^ :: Equiv ...


-- Add Context ------------------------------------------------------------

addInPat :: AddPat p s g g' -> InPat p s g'
addInPat (AddVar pfA)    = InVar   $ addIn pfA
addInPat (AddTuple pfAs) = InTuple $ addInPats pfAs


addInPats :: AddPats ps ts g g' -> InPats ps ts g'
addInPats (AddPatsNil _) = InNil
addInPats (AddPatsCons pfA pfAs) = InCons pfD pfI' pfIs
  where
 -- pfA  :: AddPat p t g g0
 -- pfAs :: AddPats ps' ts' g0 g'
 -- want :: InPats (p:ps') (t:ts') g'

 -- pfI :: InPat p t g0
    pfI  = addInPat pfA
 -- pfI' :: InPat p t g'
    pfI' = inPatAddPatsIn pfI pfAs
 -- pfIs :: InPats ps' ts' g'
    pfIs = addInPats pfAs
 -- pfD :: DisjointPatPats ps' p
    pfD = addPatPatsDisjoint pfA pfAs


-- Remove -----------------------------------------------

-- addEquivRemove 
-- for any g, g ~ Remove x (g[x |-> s])
addEquivRemove :: AddCtx x s g g' -> Equiv g (Remove x g')
addEquivRemove AddEHere        = EquivEL $ EmptyCons EmptyNil
addEquivRemove (AddHere g0)    = EquivCons $ equivRefl g0
addEquivRemove (AddELater pfA) = EquivEL $ EmptyCons $ emptyRemove EmptyNil pfA
addEquivRemove (AddLater pfA)  = EquivCons $ addEquivRemove pfA

addPatEquivRemove :: AddPat p t g g' -> Equiv g (RemovePat p g')
addPatEquivRemove (AddVar pfA)    = addEquivRemove pfA
addPatEquivRemove (AddTuple pfAs) = addPatsEquivRemove pfAs

addPatsEquivRemove :: AddPats ps ts g g' -> Equiv g (RemovePats ps g')
addPatsEquivRemove (AddPatsNil g) = equivRefl g
addPatsEquivRemove (AddPatsCons pfA pfAs) = equivTrans pfE pfEs'
  where
    -- ps=p:ps'
    -- ts=t:ts'
    -- pfA :: AddPat p t g g0
    -- pfAs :: AddPats ps ts g0 g'
    -- addPatEquivRemove pfA :: Equiv g (RemovePat p g0)
    -- addPatsEquivRemove pfAs :: Equiv g0 (RemovePats ps' g')
    -- inPatsEquivRemove ^ :: Equiv (RemovePat p g0) (RemovePat p (RemovePats ps' g'))
    -- equivTrans ^3 ^1 :: Equiv g (RemovePat p (RemovePats ps' g'))
    pfE   = addPatEquivRemove pfA
    pfEs  = addPatsEquivRemove pfAs
    pfEs' = inPatEquivRemove (addPatIn pfA) pfEs
-------------------

emptyRemove :: EmptyCtx g -> AddCtx x s g g' -> EmptyCtx (Remove x g')
emptyRemove pfE pfA = equivEmpty pfE (addEquivRemove pfA)

emptyRemovePat :: EmptyCtx g -> AddPat p s g g' -> EmptyCtx (RemovePat p g')
emptyRemovePat pfE pfA = equivEmpty pfE (addPatEquivRemove pfA)

emptyRemovePats :: EmptyCtx g -> AddPats ps ts g g' -> EmptyCtx (RemovePats ps g')
emptyRemovePats pfE pfAs = equivEmpty pfE (addPatsEquivRemove pfAs)

-- SingletonCtx -----------------------------------------------

singletonEmpty :: SingletonCtx x s g -> EmptyCtx (Remove x g)
singletonEmpty AddHereS        = EmptyCons EmptyNil
singletonEmpty (AddLaterS pfS) = EmptyCons $ singletonEmpty pfS

singS :: NatS x -> SingletonCtx x s (Sing x s)
singS ZS = AddHereS
singS (SS x) = AddLaterS $ singS x


singletonAdd :: SingletonCtx x s g -> AddCtx x s '[] g
singletonAdd AddHereS        = AddEHere
singletonAdd (AddLaterS pfS) = AddELater (singletonAdd pfS)

addSingleton :: AddCtx x s '[] g' -> SingletonCtx x s g'
addSingleton AddEHere        = AddHereS
addSingleton (AddELater pfA) = AddLaterS $ addSingleton pfA


singletonInInv :: In x s g
               -> SingletonCtx y t g
               -> Dict ('(x,s)~'(y,t))
singletonInInv (InHere _)    AddHereS        = Dict
singletonInInv (InLater pfI) (AddLaterS pfS) = 
  case singletonInInv pfI pfS of Dict -> Dict


-- Relationship between NotIn and Add -----------------

notInAdd :: NotIn x g -> AddCtx x s g (AddFun x s g)
notInAdd (NotInNil x)     = singletonAdd (singS x)
notInAdd (NotInHere g)    = AddHere g
notInAdd (NotInLater pfN) = AddLater $ notInAdd pfN

addNotIn :: AddCtx x s g g' -> NotIn x g
addNotIn AddEHere        = NotInNil ZS
addNotIn (AddHere g)     = NotInHere g
addNotIn (AddELater pfA) = NotInNil . SS $ addToNatS pfA
addNotIn (AddLater pfA)  = NotInLater $ addNotIn pfA


-- Relationship between In and Add --------------------------------------
-- if x ∈ g and you can add y to g then you can add y to (Remove x g) ---

inRemove :: In x s g 
         -> AddCtx x s (Remove x g) g
inRemove = undefined

inAddRemove :: In x s g
            -> AddCtx y t g g'
            -> AddCtx y t (Remove x g) (Remove x g')
inAddRemove (InHere _)    (AddLater pfA) = AddLater pfA
inAddRemove (InLater pfI) (AddHere pf)   = AddHere  $ inSCtxRemove pfI pf
inAddRemove (InLater pfI) (AddLater pfA) = AddLater $ inAddRemove pfI pfA

inAddPatRemove :: In x s g 
             -> AddPat p t g g'
             -> AddPat p t (Remove x g) (Remove x g')
inAddPatRemove pfI (AddVar  pfA)       = AddVar $ inAddRemove pfI pfA
inAddPatRemove pfI (AddTuple pfAs)     = AddTuple $ inAddPatsRemove pfI pfAs

inAddPatsRemove :: In x s g 
                -> AddPats ps ts g g'
                -> AddPats ps ts (Remove x g) (Remove x g')
inAddPatsRemove pfI (AddPatsNil p)         = AddPatsNil $ inSCtxRemove pfI p
inAddPatsRemove pfI (AddPatsCons pfA pfAs) = 
    AddPatsCons (inAddPatRemove pfI pfA) (inAddPatsRemove pfI' pfAs)
  where
    pfI' = inAddPatIn pfI pfA

inAddPatsRemovePat :: InPat p t g
                 -> AddPats ps ts g g'
                 -> AddPats ps ts (RemovePat p g) (RemovePat p g')
inAddPatsRemovePat (InVar pfI) pfA = inAddPatsRemove pfI pfA
inAddPatsRemovePat (InTuple pfIs) pfA = inAddPatsRemovePats pfIs pfA

inAddPatsRemovePats :: InPats ps ts g
                    -> AddPats ps' ts' g g'
                    -> AddPats ps' ts' (RemovePats ps g) (RemovePats ps g')
inAddPatsRemovePats InNil pfAs = pfAs
inAddPatsRemovePats (InCons pfD pfI pfIs) pfAs = 
  inAddPatsRemovePat pfI' $ inAddPatsRemovePats pfIs pfAs
  where
    pfI' = disjointPatPatsIn pfD pfI pfIs

-- if p is in g and p' gets added to g then p is still in the result

inAdd :: In x s g -> AddCtx y t g g' -> In x s g'
inAdd (InHere g0)   (AddLater pfA) = InHere $ addSCtx pfA g0
inAdd (InLater pfI) (AddHere _)    = InLater pfI
inAdd (InLater pfI) (AddLater pfA) = InLater $ inAdd pfI pfA


inPatAddIn :: InPat p t g -> AddCtx x s g g' -> InPat p t g'
inPatAddIn (InVar pfI) pfA = InVar $ inAdd pfI pfA
inPatAddIn (InTuple pfIs) pfA = InTuple $ inPatsAddIn pfIs pfA

inPatsAddIn :: InPats ps ts g -> AddCtx x s g g' -> InPats ps ts g'
inPatsAddIn InNil                 _   = InNil
inPatsAddIn (InCons pfD pfI pfIs) pfA = InCons pfD pfI' pfIs' 
  where
    pfI'  = inPatAddIn pfI pfA
    pfIs' = inPatsAddIn pfIs pfA


inPatAddPatIn :: InPat p t g -> AddPat p' t' g g' -> InPat p t g'
inPatAddPatIn pfI (AddVar pfA)    = inPatAddIn pfI pfA
inPatAddPatIn pfI (AddTuple pfAs) = inPatAddPatsIn pfI pfAs

inPatAddPatsIn :: InPat p t g -> AddPats ps ts g g' -> InPat p t g'
inPatAddPatsIn pfI (AddPatsNil _)         = pfI
inPatAddPatsIn pfI (AddPatsCons pfA pfAs) = pfIs'
  where
    pfI' = inPatAddPatIn pfI pfA
    pfIs' = inPatAddPatsIn pfI' pfAs

inAddPatIn :: In x s g -> AddPat p t g g' -> In x s g'
inAddPatIn pfI (AddVar pfA)        = inAdd pfI pfA
inAddPatIn pfI (AddTuple pfAs)     = inAddPatsIn pfI pfAs

inAddPatsIn :: In x s g -> AddPats ps ts g g' -> In x s g'
inAddPatsIn pfI (AddPatsNil _)         = pfI
inAddPatsIn pfI (AddPatsCons pfA pfAs) = inAddPatsIn (inAddPatIn pfI pfA) pfAs


-- Disjointness -------------------------------

disjointPatPatSymm :: DisjointPatPat p p'
                   -> DisjointPatPat p' p
disjointPatPatSymm = undefined


disjointInIn :: Disjoint x y
             -> In x s g
             -> In y t g
             -> In x s (Remove y g)
disjointInIn DisjointZS      (InHere g)     (InLater pfI)  = InHere $ inSCtxRemove pfI g
disjointInIn DisjointSZ      (InLater pfI)  (InHere _)     = InLater pfI
disjointInIn (DisjointS pfD) (InLater pfIx) (InLater pfIy) = 
    InLater $ disjointInIn pfD pfIx pfIy

disjointPatIn :: DisjointPat x p
              -> In x s g
              -> InPat p t g
              -> In x s (RemovePat p g)
disjointPatIn (DisjointIdent pfD) pfI (InVar pfI')   = disjointInIn pfD pfI pfI'
disjointPatIn (DisjointTup pfDs)  pfI (InTuple pfIs) = disjointPatsIn pfDs pfI pfIs

disjointPatsIn :: DisjointPats x ps
               -> In x s g
               -> InPats ps ts g
               -> In x s (RemovePats ps g)
disjointPatsIn (DisjointPatsNil) pfI (InNil) = pfI
disjointPatsIn (DisjointPatsCons pfD pfDs) pfI (InCons pfD0 pfI' pfIs') = 
  disjointPatIn pfD (disjointPatsIn pfDs pfI pfIs') pfI''
  where
    pfI'' = disjointPatPatsIn pfD0 pfI' pfIs'

disjointPatPatIn :: DisjointPatPat p p'
                 -> InPat p s g
                 -> InPat p' s' g
                 -> InPat p s (RemovePat p' g)
disjointPatPatIn (DisjointPatIdent pfD) (InVar pfI)    pfI' = 
    InVar $ disjointPatIn pfD pfI pfI'
disjointPatPatIn (DisjointPatTup  pfDs) (InTuple pfIs) pfI' = 
    InTuple $ disjointPatsPatIn pfDs pfIs pfI'

disjointPatsPatIn :: DisjointPatPats ps p
                  -> InPats ps ts g
                  -> InPat p t g
                  -> InPats ps ts (RemovePat p g)
disjointPatsPatIn DisjointPatPatsNil InNil pfI = InNil
disjointPatsPatIn (DisjointPatPatsCons pfD pfDs) (InCons pfD0 pfI' pfIs') pfI = 
  InCons pfD0 pfI'' pfIs'' 
  where
    pfI'' = disjointPatPatIn pfD pfI' pfI
    pfIs'' = disjointPatsPatIn pfDs pfIs' pfI

disjointPatPatsIn :: DisjointPatPats ps p
                  -> InPat p s g
                  -> InPats ps ts g
                  -> InPat p s (RemovePats ps g)
disjointPatPatsIn DisjointPatPatsNil             pfI _    = pfI
disjointPatPatsIn (DisjointPatPatsCons pfD pfDs) pfI (InCons pfDs' pfI' pfIs') = pfIR'
  where
    -- ps=p1:ps2
    -- pfD   :: DisjointPatPat p1 p
    -- pfDs  :: DisjointPatPats ps2 p
    -- pfDs' :: DisjointPats p1 ps2
    -- pfI   :: InPat p s g
    -- pfI'  :: InPat p1 t1 g
    -- pfIs' :: InPats ps2 ts2 g
    -- pfIR :: InPat p s (RemovePats ps2 g)
    pfIR = disjointPatPatsIn pfDs pfI pfIs'
    -- pfIRs :: InPat p1 t1 (RemovePats ps2 g)
    pfIRs = disjointPatPatsIn pfDs' pfI' pfIs'
    -- _ :: InPat p s (RemovePat p1 (RemovePats ps2 g)
    pfIR' = disjointPatPatIn pfD' pfIR pfIRs
    pfD'  = disjointPatPatSymm pfD

addDisjoint :: AddCtx x s g g'
            -> DisjointCtx x g
addDisjoint AddEHere        = DisjointNil
addDisjoint (AddHere _)     = DisjointHere
addDisjoint (AddELater _)   = DisjointNil
addDisjoint (AddLater pfA)  = DisjointLater $ addDisjoint pfA

addPatDisjoint :: AddPat p t g g'
               -> DisjointPatCtx p g
addPatDisjoint (AddVar pfA)    = DisjointPatIdentCtx $ addDisjoint pfA
addPatDisjoint (AddTuple pfAs) = DisjointPatTupleCtx $ addPatsDisjoint pfAs

addPatsDisjoint :: AddPats ps ts g g'
                -> DisjointPatsCtx ps g
addPatsDisjoint (AddPatsNil _)         = DisjointPatsCtxNil
addPatsDisjoint (AddPatsCons pfA pfAs) = DisjointPatsCtxCons pfD pfDs'
  where
    -- pfA :: AddPat p t g g0
    -- pfAs :: AddPats ps' ts' g0 g'
    -- pfDs :: DisjointPatsCtx ps' g0
    pfDs = addPatsDisjoint pfAs
    -- pfDs':: DisjointPatsCtx ps' g
    pfDs' = disjointAddTrans pfDs pfA
    -- pfD :: DisjointPatCtx p g
    pfD = addPatDisjoint pfA

-- proving things are disjoint

disjointAddTrans :: DisjointPatsCtx ps g'
                 -> AddPat p t g g'
                 -> DisjointPatsCtx ps g
disjointAddTrans = undefined


disjointIn :: DisjointCtx x g
           -> In y s g
           -> Disjoint x y
disjointIn (DisjointHere)      (InLater _)   = DisjointZS
disjointIn (DisjointLater _)   (InHere _)    = DisjointSZ
disjointIn (DisjointLater pfD) (InLater pfI) = DisjointS $ disjointIn pfD pfI

disjointInPat :: DisjointCtx x g
              -> InPat p s g
              -> DisjointPat x p
disjointInPat pfD (InVar pfI) = DisjointIdent $ disjointIn pfD pfI
disjointInPat pfD (InTuple pfI) = DisjointTup $ disjointInPats pfD pfI

disjointInPats :: DisjointCtx x g
               -> InPats ps ts g
               -> DisjointPats x ps
disjointInPats pfD InNil = DisjointPatsNil
disjointInPats pfD (InCons _ pfI pfIs) = 
  DisjointPatsCons (disjointInPat pfD pfI) (disjointInPats pfD pfIs)

disjointPatInPat :: DisjointPatCtx p g
                 -> InPat p' s g
                 -> DisjointPatPat p p'
disjointPatInPat (DisjointPatIdentCtx pfD)  pfI = DisjointPatIdent $ disjointInPat pfD pfI
disjointPatInPat (DisjointPatTupleCtx pfDs) pfI = DisjointPatTup   $ disjointPatsInPat pfDs pfI

disjointPatsInPat :: DisjointPatsCtx ps g
                  -> InPat p s g
                  -> DisjointPatPats ps p
disjointPatsInPat DisjointPatsCtxNil             pfI = DisjointPatPatsNil
disjointPatsInPat (DisjointPatsCtxCons pfD pfDs) pfI = DisjointPatPatsCons pfD' pfDs'
  where
    pfD'  = disjointPatInPat pfD pfI
    pfDs' = disjointPatsInPat pfDs pfI

addPatPatsDisjoint :: forall p ps t ts g1 g2 g3. 
                      AddPat p t g1 g2
                   -> AddPats ps ts g2 g3
                   -> DisjointPatPats ps p
addPatPatsDisjoint pfA pfAs = disjointPatsInPat pfD pfI
  where
    pfI :: InPat p t g2
    pfI = addPatIn pfA
    pfD :: DisjointPatsCtx ps g2
    pfD = addPatsDisjoint pfAs

-- Merge ----------------------------------------------------

mergeEmpty3 :: forall g. EmptyCtx g -> Merge g g g
mergeEmpty3 EmptyNil = MergeE
mergeEmpty3 (EmptyCons pfEmpty) = MergeU (mergeEmpty3 pfEmpty)

mergeEmpty :: forall g1 g2 g. 
              Merge g1 g2 g 
           -> EmptyCtx g 
           -> (EmptyCtx g1, EmptyCtx g2)
mergeEmpty MergeE        EmptyNil       = (EmptyNil, EmptyNil)
mergeEmpty MergeEL       pfEmpty        = (EmptyNil, pfEmpty)
mergeEmpty MergeER       pfEmpty        = (pfEmpty, EmptyNil)
mergeEmpty (MergeU pfM) (EmptyCons pfE) = 
  let (pfE1, pfE2) = mergeEmpty pfM pfE 
  in (EmptyCons pfE1, EmptyCons pfE2)

{-
mergeSCtx :: Merge g1 g2 g -> SCtx g -> (SCtx g1, SCtx g2)
mergeSCtx MergeE _ = (SNil,SNil)
mergeSCtx MergeEL g = (SNil,g)
mergeSCtx MergeER g = (g,SNil)
mergeSCtx (MergeL pfM) (SCons u g) = 
  let (g1',g2') = mergeSCtx pfM g 
  in  (SCons u g1', SCons SUnused g2')
mergeSCtx (MergeR pfM) (SCons u g) = 
  let (g1',g2') = mergeSCtx pfM g
  in (SCons SUnused g1', SCons u g2')
mergeSCtx (MergeU pfM) (SCons _ g) = 
  let (g1',g2') = mergeSCtx pfM g
  in (SCons SUnused g1', SCons SUnused g2')
-}

-- might need more infrascructure
mergeSCtx1 :: Merge g1 g2 g -> SCtx g1
mergeSCtx1 = undefined

mergeSCtx2 :: Merge g1 g2 g -> SCtx g2
mergeSCtx2 = undefined

mergeSCtx :: Merge g1 g2 g -> SCtx g
mergeSCtx = undefined

-- In ---------------------------------------------------

addIn :: AddCtx x s g g' -> In x s g'
addIn AddEHere       = InHere SNil
addIn (AddHere g)    = InHere g
addIn (AddELater pf) = InLater $ addIn pf
addIn (AddLater pf)  = InLater $ addIn pf

addPatIn :: AddPat p t g g' -> InPat p t g'
addPatIn (AddVar pfA)    = InVar $ addIn pfA
addPatIn (AddTuple pfAs) = InTuple $ addPatsIn pfAs

addPatsIn :: AddPats ps ts g g' -> InPats ps ts g'
addPatsIn (AddPatsNil _)         = InNil
addPatsIn (AddPatsCons pfA pfAs) = InCons pfD pfI pfIs
  where
  -- pfA  :: AddPat p t g g0
  -- pfAs :: AddPats ps' ts' g0 g'
  -- addPatIn  pfA  :: InPat p t g0
  -- inPatAddPatsIn ^ pfAs :: InPat p t g'
     pfI = inPatAddPatsIn (addPatIn pfA) pfAs
  -- addPatsIn pfAs :: InPats ps' ts' g'
     pfIs = addPatsIn pfAs
  -- pfD :: DisjointPatPats p ps'
     pfD = addPatPatsDisjoint pfA pfAs

inEmptyAbsurd :: In x s g -> EmptyCtx g -> a
inEmptyAbsurd (InLater pfI) (EmptyCons pfE) = inEmptyAbsurd pfI pfE

-- Relation between In and Shift

inShift :: In x s g
        -> Shift i g' g
        -> In (InShift x i) s g'
inShift (InLater pfI) ShiftHere = pfI
inShift (InHere g0)   (ShiftLater pfS) = InHere $ unshiftSCtx pfS g0
inShift (InLater pfI) (ShiftLater pfS) = InLater $ inShift pfI pfS

inUnshift :: In x s g
          -> Shift i g g'
          -> In (InUnshift x i) s g'
inUnshift pfI           ShiftHere        = InLater pfI
inUnshift (InHere g)    (ShiftLater pfS) = InHere $ shiftSCtx pfS g
inUnshift (InLater pfI) (ShiftLater pfS) = InLater $ inUnshift pfI pfS


shiftRemove :: Shift i g g'
            -> In (InShift x i) s g
            -> In x t g'
            -> Shift i (Remove (InShift x i) g) (Remove x g')
-- i=Z
-- g'=Unused:g
-- x=S y
-- pfI' = In y t g
-- Remove y g' = Unused:Remove y g
-- InShift x i = y
-- Remove (InShift x i) g = Remove y g
shiftRemove ShiftHere        pfI (InLater pfI') = ShiftHere
-- i=S j
-- g=Used s:g0
-- pfS :: Shift j g0 g0'
-- x=Z
-- g'=Used s:g0'
-- InShift x i = InShift Z (S j) = Z
-- Remove (InShift x i) g = Remove Z (Used s : g0) = Unused : g0
-- Remove x g' = Remove Z (Used s : g0') = Unused : g0'
shiftRemove (ShiftLater pfS) pfI (InHere _)        = ShiftLater pfS
-- i=S j
-- g=u:g0
-- g'=u:g0'
-- pfS :: Shift j g0 g0'
-- x=S y
-- pfI' :: In y s g0'
-- InShift x i = InShift (S y) (S j) = S (InShift y j)
-- pfI :: In (InShift y j) g0
-- shiftREmove pfS pfI pfI' :: Shift j (Remove (InShift y j) g0) (Remove y g0')
-- want: Shift (S j) (Remove (S (InShift y j)) (u:g0)) (Remove (S y) (u:g0'))
--     = Shift (S j) (u:Remove (InShift y j) g0) (u:Remove y g0')
shiftRemove (ShiftLater pfS) (InLater pfI) (InLater pfI') = 
    ShiftLater $ shiftRemove pfS pfI pfI'

unshiftRemove :: Shift i g g'
              -> In x s g
              -> In (InUnshift x i) t g'
              -> Shift i (Remove x g) (Remove (InUnshift x i) g')
unshiftRemove ShiftHere        (InLater pfI) pfI'           = ShiftHere
unshiftRemove (ShiftLater pfS) (InHere g)    pfI'           = ShiftLater pfS
unshiftRemove (ShiftLater pfS) (InLater pfI) (InLater pfI') = 
    ShiftLater $ unshiftRemove pfS pfI pfI'


-- Relation between In and Merge

mergeInSplit :: Merge g1 g2 g
             -> In x s g
             -> Either (In x s g1) (In x s g2)
mergeInSplit MergeEL      (InHere g) = Right $ InHere g
mergeInSplit MergeER      (InHere g) = Left $ InHere g
-- g1=Used s:g1'
-- g2=Unused:g2'
-- g =Used s:g'
-- pfM :: Merge g1' g2' g'
-- g :: SCtx g'
mergeInSplit (MergeL pfM) (InHere g) = Left . InHere $ mergeSCtx1 pfM
mergeInSplit (MergeR pfM) (InHere g) = Right . InHere $ mergeSCtx2 pfM
mergeInSplit MergeEL      (InLater pfI) = Right $ InLater pfI
mergeInSplit MergeER      (InLater pfI) = Left  $ InLater pfI
mergeInSplit (MergeL pfM) (InLater pfI) = 
  case mergeInSplit pfM pfI of
    Left  pfI' -> Left  $ InLater pfI'
    Right pfI' -> Right $ InLater pfI'
mergeInSplit (MergeR pfM) (InLater pfI) = 
  case mergeInSplit pfM pfI of
    Left  pfI' -> Left  $ InLater pfI'
    Right pfI' -> Right $ InLater pfI'
mergeInSplit (MergeU pfM) (InLater pfI) = 
  case mergeInSplit pfM pfI of
    Left  pfI' -> Left  $ InLater pfI'
    Right pfI' -> Right $ InLater pfI'


mergeIn1 :: Merge g1 g2 g3
         -> In x s g1
         -> Merge (Remove x g1) g2 (Remove x g3)
mergeIn1 MergeER _ = MergeER
mergeIn1 (MergeL pfM) (InHere g2)    = MergeU pfM
mergeIn1 (MergeL pfM) (InLater pfI1) = MergeL $ mergeIn1 pfM pfI1 
mergeIn1 (MergeR pfM) (InLater pfI1) = MergeR $ mergeIn1 pfM pfI1 
mergeIn1 (MergeU pfM) (InLater pfI1) = MergeU $ mergeIn1 pfM pfI1 

mergeIn2 :: Merge g1 g2 g3
         -> In x s g2
         -> Merge g1 (Remove x g2) (Remove x g3)
mergeIn2 MergeEL _ = MergeEL
mergeIn2 (MergeR pfM) (InHere g2')   = MergeU pfM
mergeIn2 (MergeL pfM) (InLater pfI2) = MergeL $ mergeIn2 pfM pfI2 
mergeIn2 (MergeR pfM) (InLater pfI2) = MergeR $ mergeIn2 pfM pfI2 
mergeIn2 (MergeU pfM) (InLater pfI2) = MergeU $ mergeIn2 pfM pfI2 


mergeInPat2 :: Merge g1 g2 g
            -> InPat p t g2
            -> Merge g1 (RemovePat p g2) (RemovePat p g)
mergeInPat2 pfM (InVar pfI)    = mergeIn2 pfM pfI
mergeInPat2 pfM (InTuple pfIs) = mergeInPats2 pfM pfIs

mergeInPats2 :: Merge g1 g2 g
             -> InPats ps ts g2
             -> Merge g1 (RemovePats ps g2) (RemovePats ps g)
mergeInPats2 pfM InNil = pfM
mergeInPats2 pfM (InCons pfD pfI pfIs) = mergeInPat2 pfM' pfI'
  where
  -- pfD :: Disjoint p ps'
  -- pfI :: InPat p t g2
  -- pfIs :: InPats ps' ts' g2
  -- mergeInPats2 pfM pfIs :: Merge g1 (RemovePats ps' g2) (RemovePats ps' g2)
  pfM' = mergeInPats2 pfM pfIs
  -- pfI' :: InPat p t (RemovePats ps' g2)
  pfI' = disjointPatPatsIn pfD pfI pfIs


-- In Merge In

inMerge1 :: In x s g1
         -> Merge g1 g2 g3
         -> In x s g3
inMerge1 (InHere g)    MergeER      = InHere g
inMerge1 (InHere g)    (MergeL pfM) = InHere $ mergeSCtx pfM
inMerge1 (InLater pfI) MergeER      = InLater pfI
inMerge1 (InLater pfI) (MergeL pfM) = InLater $ inMerge1 pfI pfM
inMerge1 (InLater pfI) (MergeR pfM) = InLater $ inMerge1 pfI pfM
inMerge1 (InLater pfI) (MergeU pfM) = InLater $ inMerge1 pfI pfM

inMerge2 :: In x s g2
         -> Merge g1 g2 g3
         -> In x s g3
inMerge2 (InHere g)    MergeEL      = InHere g
inMerge2 (InHere g)    (MergeR pfM) = InHere $ mergeSCtx pfM
inMerge2 (InLater pfI) MergeEL      = InLater pfI
inMerge2 (InLater pfI) (MergeL pfM) = InLater $ inMerge2 pfI pfM
inMerge2 (InLater pfI) (MergeR pfM) = InLater $ inMerge2 pfI pfM
inMerge2 (InLater pfI) (MergeU pfM) = InLater $ inMerge2 pfI pfM


inPatMerge1 :: InPat p s g1
            -> Merge g1 g2 g3
            -> InPat p s g3
inPatMerge1 (InVar pfI)    pfM = InVar   $ inMerge1 pfI pfM
inPatMerge1 (InTuple pfIs) pfM = InTuple $ inPatsMerge1 pfIs pfM

inPatMerge2 :: InPat p s g2
         -> Merge g1 g2 g3
         -> InPat p s g3
inPatMerge2 (InVar pfI)    pfM = InVar   $ inMerge2 pfI pfM
inPatMerge2 (InTuple pfIs) pfM = InTuple $ inPatsMerge2 pfIs pfM


inPatsMerge1 :: InPats ps ts g1
             -> Merge g1 g2 g3
             -> InPats ps ts g3
inPatsMerge1 InNil                 pfM = InNil
inPatsMerge1 (InCons pfD pfI pfIs) pfM = InCons pfD pfI' pfIs'
  where
    pfI'  = inPatMerge1  pfI pfM
    pfIs' = inPatsMerge1 pfIs pfM

inPatsMerge2 :: InPats ps ts g2
             -> Merge g1 g2 g3
             -> InPats ps ts g3
inPatsMerge2 InNil                 pfM = InNil
inPatsMerge2 (InCons pfD pfI pfIs) pfM = InCons pfD pfI' pfIs'
  where
    pfI'  = inPatMerge2  pfI pfM
    pfIs' = inPatsMerge2 pfIs pfM


