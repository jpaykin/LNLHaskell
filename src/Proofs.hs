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

-- Freshness


-- Shift ---------------------------------------------------

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


-- Equivalent Contexts ------------------------------------------

equivRefl :: SCtx g -> Equiv g g
equivRefl SNil        = EquivNil
equivRefl (SCons u g) = EquivCons $ equivRefl g

equivSymm :: Equiv g g' -> Equiv g' g
equivSymm EquivNil = EquivNil
equivSymm (EquivEL pf) = EquivER pf
equivSymm (EquivER pf) = EquivEL pf
equivSymm (EquivCons pfE) = EquivCons $ equivSymm pfE

--addToSing :: AddCtx x s g g' -> SCtx g
-- addToSing AddEHere = SNil
-- addToSing AddHere  = SNil

equivNilL :: Equiv '[] g -> EmptyCtx g
equivNilL EquivNil      = EmptyNil
equivNilL (EquivEL pfE) = pfE
equivNilL (EquivER _)   = EmptyNil

equivTrans :: Equiv g1 g2 -> Equiv g2 g3 -> Equiv g1 g3
equivTrans EquivNil          pfEq = pfEq
equivTrans (EquivEL pfE)     pfEq = EquivEL $ equivEmpty pfE pfEq
equivTrans (EquivER pfE1)    pfEq = emptyEquiv pfE1 $ equivNilL pfEq
equivTrans (EquivCons pfEq1) (EquivER (EmptyCons pfE2)) = 
  EquivER $ EmptyCons $ equivEmpty pfE2 $ equivSymm pfEq1
equivTrans (EquivCons pfEq1) (EquivCons pfEq2) = EquivCons $ equivTrans pfEq1 pfEq2

addRemoveEquiv :: AddCtx x s g g'
               -> Equiv g (Remove x g')
addRemoveEquiv AddEHere        = EquivEL $ EmptyCons EmptyNil
addRemoveEquiv (AddHere g0)     = EquivCons $ equivRefl g0
addRemoveEquiv (AddELater pfA) = EquivEL $ EmptyCons $ addRemoveEmpty EmptyNil pfA
addRemoveEquiv (AddLater pfA)  = EquivCons $ addRemoveEquiv pfA

addRemoveEmpty :: EmptyCtx g -> AddCtx x s g g' -> EmptyCtx (Remove x g')
addRemoveEmpty _                AddEHere       = EmptyCons EmptyNil
addRemoveEmpty _               (AddELater pfA) = EmptyCons $ addRemoveEmpty EmptyNil pfA
addRemoveEmpty pfE             (AddHere _)     = pfE
addRemoveEmpty (EmptyCons pfE) (AddLater pfA)  = EmptyCons $ addRemoveEmpty pfE pfA

emptyEquiv :: EmptyCtx g -> EmptyCtx g' -> Equiv g g'
emptyEquiv EmptyNil EmptyNil = EquivNil
emptyEquiv EmptyNil pfE      = EquivEL pfE
emptyEquiv pfE EmptyNil      = EquivER pfE
emptyEquiv (EmptyCons pfE) (EmptyCons pfE') = EquivCons $ emptyEquiv pfE pfE'

equivEmpty :: EmptyCtx g -> Equiv g g' -> EmptyCtx g'
equivEmpty EmptyNil        EquivNil         = EmptyNil
equivEmpty EmptyNil        (EquivEL pfE)    = pfE
equivEmpty _               (EquivER _)      = EmptyNil
equivEmpty (EmptyCons pfE) (EquivCons pfEq) = EmptyCons $ equivEmpty pfE pfEq

inSCtxRemove :: In x s g -> SCtx g -> SCtx (Remove x g)
inSCtxRemove (InHere g') g = SCons SUnused g'
inSCtxRemove (InLater pfI) (SCons u g') = SCons u $ inSCtxRemove pfI g'

-- Empty Context ----------------------------------------------

-- Add To Context ----------------------------------------------


sCtxAdd :: forall y t g g'. 
           SCtx g
        -> AddCtx y t g g'
        -> SCtx g'
sCtxAdd g            AddEHere        = SCons (SUsed @t) g
sCtxAdd _            (AddHere g')    = SCons (SUsed @t) g'
sCtxAdd g            (AddELater pfA) = SCons SUnused $ sCtxAdd g pfA
sCtxAdd (SCons u g0) (AddLater pfA)  = SCons u $ sCtxAdd g0 pfA

inAdd :: In x s g
      -> AddCtx y t g g'
      -> In x s g'
inAdd (InHere g0)   (AddLater pfA) = InHere $ sCtxAdd g0 pfA
inAdd (InLater pfI) (AddHere _)    = InLater pfI
inAdd (InLater pfI) (AddLater pfA) = InLater $ inAdd pfI pfA

inAddRemove :: In x s g
            -> AddCtx y t g g'
            -> AddCtx y t (Remove x g) (Remove x g')
inAddRemove (InHere _)    (AddLater pfA) = AddLater pfA
inAddRemove (InLater pfI) (AddHere pf)   = AddHere  $ inSCtxRemove pfI pf
inAddRemove (InLater pfI) (AddLater pfA) = AddLater $ inAddRemove pfI pfA


singletonAdd :: SingletonCtx x s g -> AddCtx x s '[] g
singletonAdd AddHereS        = AddEHere
singletonAdd (AddLaterS pfS) = AddELater (singletonAdd pfS)

addSingleton :: AddCtx x s '[] g' -> SingletonCtx x s g'
addSingleton AddEHere        = AddHereS
addSingleton (AddELater pfA) = AddLaterS $ addSingleton pfA

addToSIdent :: AddCtx x s g g' -> SIdent x
addToSIdent = undefined

-- Singleton Context ------------------------------------------

singletonEmpty :: SingletonCtx x s g
               -> EmptyCtx (Remove x g)
singletonEmpty AddHereS        = EmptyCons EmptyNil
singletonEmpty (AddLaterS pfS) = EmptyCons $ singletonEmpty pfS

fSingletonCtx :: SIdent x -> SingletonCtx x s (FSingletonCtx x s)
fSingletonCtx SZ = AddHereS
fSingletonCtx (SS x) = AddLaterS $ fSingletonCtx x

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

-- Remove ------------------------------------------

emptyRemove :: EmptyCtx g
            -> AddCtx x s g g'
            -> EmptyCtx (Remove x g')
emptyRemove EmptyNil        AddEHere        = EmptyCons EmptyNil
emptyRemove EmptyNil        (AddELater pfA) = EmptyCons $ emptyRemove EmptyNil pfA
emptyRemove pfE             (AddHere _)     = pfE
emptyRemove (EmptyCons pfE) (AddLater pfA)  = EmptyCons $ emptyRemove pfE pfA


-- In -------------------------------

addIn :: AddCtx x s g g' -> In x s g'
addIn AddEHere       = InHere SNil
addIn (AddHere g)    = InHere g
addIn (AddELater pf) = InLater $ addIn pf
addIn (AddLater pf)  = InLater $ addIn pf

inEmptyAbsurd :: In x s g -> EmptyCtx g -> a
inEmptyAbsurd (InLater pfI) (EmptyCons pfE) = inEmptyAbsurd pfI pfE


singletonInInv :: In x s g
               -> SingletonCtx y t g
               -> Dict ('(x,s)~'(y,t))
singletonInInv (InHere _)    AddHereS        = Dict
singletonInInv (InLater pfI) (AddLaterS pfS) = 
  case singletonInInv pfI pfS of Dict -> Dict

inRemove :: In x s g
         -> AddCtx x s (Remove x g) g
inRemove (InHere g) = AddHere g
inRemove (InLater pfIn) = AddLater $ inRemove pfIn

-- Relation between In and Shift

inShift :: In x s g
        -> Shift i g' g
        -> In (InShift x i) s g'
inShift (InLater pfI) ShiftHere = pfI
inShift (InHere g0)   (ShiftLater pfS) = InHere $ unshiftSCtx pfS g0
inShift (InLater pfI) (ShiftLater pfS) = InLater $ inShift pfI pfS

type family InUnshift x i :: Nat where
  InUnshift x      'Z     = 'S x
  InUnshift 'Z     ('S i) = 'Z
  InUnshift ('S x) ('S i) = 'S (InUnshift x i)

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
mergeInSplit (MergeL pfM) (InHere g) = Left . InHere . fst $ mergeSCtx pfM g
mergeInSplit (MergeR pfM) (InHere g) = Right . InHere . snd $ mergeSCtx pfM g
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
         -> In x s g3
         -> Merge (Remove x g1) g2 (Remove x g3)
mergeIn1 MergeER _ _ = MergeER
mergeIn1 (MergeL pfM) (InHere g2)    (InHere g3)    = MergeU pfM
mergeIn1 (MergeL pfM) (InLater pfI1) (InLater pfI3) = MergeL $ mergeIn1 pfM pfI1 pfI3
mergeIn1 (MergeR pfM) (InLater pfI1) (InLater pfI3) = MergeR $ mergeIn1 pfM pfI1 pfI3
mergeIn1 (MergeU pfM) (InLater pfI1) (InLater pfI3) = MergeU $ mergeIn1 pfM pfI1 pfI3

mergeIn2 :: Merge g1 g2 g3
         -> In x s g2
         -> In x s g3
         -> Merge g1 (Remove x g2) (Remove x g3)
mergeIn2 MergeEL _ _ = MergeEL
mergeIn2 (MergeR pfM) (InHere g2')   (InHere g3')   = MergeU pfM
mergeIn2 (MergeL pfM) (InLater pfI2) (InLater pfI3) = MergeL $ mergeIn2 pfM pfI2 pfI3
mergeIn2 (MergeR pfM) (InLater pfI2) (InLater pfI3) = MergeR $ mergeIn2 pfM pfI2 pfI3
mergeIn2 (MergeU pfM) (InLater pfI2) (InLater pfI3) = MergeU $ mergeIn2 pfM pfI2 pfI3



