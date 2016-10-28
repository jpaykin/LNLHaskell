{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, DeriveLift, StandaloneDeriving
#-}

module Context where

import Data.Kind
import Data.Constraint
import Language.Haskell.TH.Syntax

import Types


-- Pattern Matching -----------------------------------------

data Pattern where
  PVar  :: Ident -> Pattern
  PTuple:: [Pattern] -> Pattern

data SPat :: Pattern -> * where
  MkVar   :: forall x. SPat ('PVar x)
  MkTuple :: SPats ps -> SPat (PTuple ps)

data SPats :: [Pattern] -> * where
  MkNil    :: SPats '[]
  MkCons   :: SPat p -> SPats ps -> SPats (p ': ps)


data AddPat :: Pattern -> LType -> Ctx -> Ctx -> * where
  AddVar  :: AddCtx x s g g' -> AddPat ('PVar x) s g g'
  AddTuple :: AddPats ps ts g g' -> AddPat (PTuple ps) (Tuple ts) g g'

data AddPats :: [Pattern] -> [LType] -> Ctx -> Ctx -> * where
  AddPatsNil :: AddPats '[] '[] g g
  AddPatsCons :: AddPat p t g1 g2 -> AddPats ps ts g2 g3 -> AddPats (p ': ps) (t ': ts) g1 g3
  

addPatRemove :: In x s g -> AddPat p t g g'
             -> AddPat p t (Remove x g) (Remove x g')
addPatRemove pfI (AddVar  pfA)       = AddVar $ inAddRemove pfI pfA
addPatRemove pfI (AddTuple pfAs)     = AddTuple $ addPatsRemove pfI pfAs

addPatsRemove :: In x s g -> AddPats ps ts g g'
              -> AddPats ps ts (Remove x g) (Remove x g')
addPatsRemove pfI AddPatsNil             = AddPatsNil
addPatsRemove pfI (AddPatsCons pfA pfAs) = 
    AddPatsCons (addPatRemove pfI pfA) (addPatsRemove pfI' pfAs)
  where
    pfI' = addPatIn pfI pfA


addPatIn :: In x s g -> AddPat p t g g' -> In x s g'
addPatIn pfI (AddVar pfA)        = inAdd pfI pfA
addPatIn pfI (AddTuple pfAs)     = addPatsIn pfI pfAs

addPatsIn :: In x s g -> AddPats ps ts g g' -> In x s g'
addPatsIn pfI AddPatsNil             = pfI
addPatsIn pfI (AddPatsCons pfA pfAs) = addPatsIn (addPatIn pfI pfA) pfAs


-- Shift -----------------------------------------------------

data Shift :: Nat -> Ctx -> Ctx -> * where
  ShiftHere  :: Shift 'Z g ('Unused ': g)
  ShiftLater :: Shift n g g' -> Shift ('S n) (u ': g) (u ': g')
deriving instance Lift (Shift i g g')

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

data Equiv  :: Ctx -> Ctx -> * where
  EquivNil  :: Equiv '[] '[]
  EquivEL   :: EmptyCtx g -> Equiv '[] g
  EquivER   :: EmptyCtx g -> Equiv g '[]
  EquivCons :: Equiv g1 g2 -> Equiv (u ': g1) (u ': g2)
deriving instance Lift (Equiv g g')

data EquivEmpty  :: Ctx -> Ctx -> * where
  EquivENil  :: EquivEmpty '[] '[]
  EquivEEL   :: EmptyCtx g -> EquivEmpty '[] g
  EquivEER   :: EmptyCtx g -> EquivEmpty g '[]
  EquivECons :: EquivEmpty g1 g2 -> EquivEmpty ('Unused ': g1) ('Unused ': g2)
deriving instance Lift (EquivEmpty g g')

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

emptyEquivEmpty :: EmptyCtx g -> EmptyCtx g' -> EquivEmpty g g'
emptyEquivEmpty EmptyNil EmptyNil = EquivENil
emptyEquivEmpty EmptyNil pfE = EquivEEL pfE
emptyEquivEmpty pfE EmptyNil = EquivEER pfE
emptyEquivEmpty (EmptyCons pfE1) (EmptyCons pfE2) = EquivECons $ emptyEquivEmpty pfE1 pfE2

-- Empty Context ------------------------------------------------

data EmptyCtx :: Ctx -> * where
  EmptyNil  :: EmptyCtx '[]
  EmptyCons :: forall x g. EmptyCtx g -> EmptyCtx ('Unused ': g)
deriving instance Lift (EmptyCtx g)

-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
-- f1++[(x,t)]++f2 is a frame for g and g'
data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddEHere   :: AddCtx 'Z s '[]            '[ 'Used s ]
  AddHere    :: SCtx g -> AddCtx 'Z s ('Unused ': g) ('Used s ': g)
  AddELater  :: AddCtx x s '[] g -> AddCtx ('S x) s '[] ('Unused ': g)
  AddLater   :: AddCtx x s g g'  -> AddCtx ('S x) s (u ': g) (u ': g')
deriving instance Lift (AddCtx x s g g')

{-
type family Insert x s g :: Ctx where
  Insert 'Z     s '[]            = '[ 'Used s ]
  Insert 'Z     s ('Unused ': g) = 'Used s ': g
  Insert ('S x) s '[]            = 'Unused ': Insert x s '[]
  Insert ('S x) s (u       ': g) = u ': Insert x s g


addInsert :: AddCtx x s g1 g2
          -> Dict (g2 ~ Insert x s g1)
addInsert AddHere         = Dict
addInsert AddEHere        = Dict
addInsert (AddELater pfA) = case addInsert pfA of Dict -> Dict
addInsert (AddLater pfA)  = case addInsert pfA of Dict -> Dict


addTwice :: AddCtx x s g1 g2
         -> AddCtx y t g2 g3
         -> (AddCtx y t g1 (Insert y t g1), AddCtx x s (Insert y t g1) g3)
addTwice AddHere           (AddLater pfAdd)  = 
         case addInsert pfAdd of Dict -> (AddLater pfAdd, AddHere)
addTwice (AddLater pfAdd)   AddHere          = 
         case addInsert pfAdd of Dict -> (AddHere, AddLater pfAdd)
addTwice (AddLater pfAdd1) (AddLater pfAdd2) = 
         let (pfAdd1', pfAdd2') = addTwice pfAdd1 pfAdd2
         in (AddLater pfAdd1', AddLater pfAdd2')
-}

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


-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
-- f1++[(x,s)]++f2 is a frame for g
data SingletonCtx :: Nat -> LType -> Ctx -> * where
  AddHereS  :: SingletonCtx 'Z s '[ 'Used s ]
  AddLaterS :: SingletonCtx x s g
            -> SingletonCtx ('S x) s ('Unused ': g)
deriving instance Lift (SingletonCtx x s g)

singletonEmpty :: SingletonCtx x s g
               -> EmptyCtx (Remove x g)
singletonEmpty AddHereS        = EmptyCons EmptyNil
singletonEmpty (AddLaterS pfS) = EmptyCons $ singletonEmpty pfS

{-
addSingletonEmpty :: forall x s g g'. 
                     AddCtx x s g g' 
                  -> SingletonCtx x s g'
                  -> EmptyCtx g
addSingletonEmpty AddHere           AddHereS          = EmptyCons EmptyNil
addSingletonEmpty AddEHere          AddHereS          = EmptyNil
addSingletonEmpty (AddLater pfAdd) (AddLaterS pfSing) = 
                  EmptyCons $ addSingletonEmpty pfAdd pfSing
addSingletonEmpty (AddELater pfAdd) (AddLaterS pfSing) = EmptyNil
-}

type family Sing x s :: Ctx where
  Sing 'Z s = '[ 'Used s ]
  Sing ('S x) s = 'Unused ': Sing x s

singS :: NatS x -> SingletonCtx x s (Sing x s)
singS ZS = AddHereS
singS (SS x) = AddLaterS $ singS x



-- Merge ----------------------------------------------------

-- merge g1 g2 g3
-- assuming g1 and g2 share a frame f, merge is functional.
data Merge :: Ctx -> Ctx -> Ctx -> * where
  MergeE  :: Merge '[] '[] '[]
  MergeEL :: Merge '[] g g
  MergeER :: Merge g '[] g
  MergeL :: Merge g1 g2 g3 
         -> Merge ('Used t ': g1) ('Unused ': g2) ('Used t ': g3)
  MergeR :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Used t ': g2) ('Used t ': g3)
  MergeU :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Unused ': g2) ('Unused ': g3)
deriving instance Lift (Merge g1 g2 g3)


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

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = 'Unused ': g
  Remove ('S x) (u ': g) = u ': Remove x g


emptyRemove :: EmptyCtx g
            -> AddCtx x s g g'
            -> EmptyCtx (Remove x g')
emptyRemove EmptyNil        AddEHere        = EmptyCons EmptyNil
emptyRemove EmptyNil        (AddELater pfA) = EmptyCons $ emptyRemove EmptyNil pfA
emptyRemove pfE             (AddHere _)     = pfE
emptyRemove (EmptyCons pfE) (AddLater pfA)  = EmptyCons $ emptyRemove pfE pfA


type family RemovePat p g :: Ctx where
  RemovePat ('PVar x) g = Remove x g
  RemovePat ('PTuple ps) g = RemovePats ps g

type family RemovePats ps g :: Ctx where
  RemovePats '[] g = g
  RemovePats (p ': ps) g = RemovePat p (RemovePats ps g)

emptyRemovePat :: EmptyCtx g
               -> AddPat p s g g'
               -> EmptyCtx (RemovePat p g')
emptyRemovePat = undefined

-- In -------------------------------

data In :: Nat -> LType -> Ctx -> * where
  InHere  :: SCtx g   -> In  'Z s ('Used s ': g)
  InLater :: In x s g -> In ('S x) s (u ': g)
deriving instance Lift (In x s g)
-- deriving instance Lift (In 'Z s ('Used s ': g))
-- deriving instance Lift (In x s g) => Lift (In ('S x) s (u ': g))

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

-- In Pat ---------------------------------------

data InPat :: Pattern -> LType -> Ctx -> * where
  InVar   :: In x s g -> InPat (PVar x) s g
  InTuple :: InPats ps ts g -> InPat (PTuple ps) (Tuple ts) g

data InPats :: [Pattern] -> [LType] -> Ctx -> * where
  InNil :: InPats '[] '[] '[]
  InCons :: Merge g1 g2 g3
         -> InPat p t g1
         -> InPats ps ts g2
         -> InPats (p ': ps) (t ': ts) g3

-- Relation between In and Shift

type family InShift x n :: Nat where
  InShift ('S x) 'Z     = x
  InShift 'Z     ('S n) = 'Z
  InShift ('S x) ('S n) = 'S (InShift x n)


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



mergeInPats :: Merge g1 g2 g
            -> InPats ps ts g2
            -> InPats ps ts g
mergeInPats = undefined

mergeInPat :: Merge g1 g2 g
           -> InPat p t g1
           -> InPat p t g
mergeInPat = undefined


mergeInPats2 :: Merge g1 g2 g
             -> InPats ps ts g2
             -> Merge g1 (RemovePats ps g2) (RemovePats ps g)
mergeInPats2 = undefined

addInPat :: AddPat p s g g' -> InPat p s g'
addInPat = undefined
