{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Context where

import Data.Kind
import Data.Constraint

import Types


-- Shift

data Shift :: Ctx -> Ctx -> * where
  ShiftHere  :: Shift g ('Unused ': g)
  ShiftLater :: Shift g g' -> Shift (u ': g) (u ': g')

shiftEmpty :: Shift g1 g2 -> EmptyCtx g1 -> EmptyCtx g2
shiftEmpty ShiftHere            pfEmpty             = EmptyCons pfEmpty  
shiftEmpty (ShiftLater pfShift) (EmptyCons pfEmpty) = EmptyCons (shiftEmpty pfShift pfEmpty)

unshiftEmpty :: Shift g1 g2 -> EmptyCtx g2 -> EmptyCtx g1
unshiftEmpty ShiftHere            (EmptyCons pfEmpty) = pfEmpty
unshiftEmpty (ShiftLater pfShift) (EmptyCons pfEmpty) = EmptyCons (unshiftEmpty pfShift pfEmpty)

-- Equivalent Contexts ------------------------------------------

data Equiv  :: Ctx -> Ctx -> * where
  EquivNil  :: Equiv '[] '[]
  EquivEL   :: EmptyCtx g -> Equiv '[] g
  EquivER   :: EmptyCtx g -> Equiv g '[]
  EquivCons :: Equiv g1 g2 -> Equiv (u ': g1) (u ': g2)

data EquivEmpty  :: Ctx -> Ctx -> * where
  EquivENil  :: EquivEmpty '[] '[]
  EquivEEL   :: EmptyCtx g -> EquivEmpty '[] g
  EquivEER   :: EmptyCtx g -> EquivEmpty g '[]
  EquivECons :: EquivEmpty g1 g2 -> EquivEmpty ('Unused ': g1) ('Unused ': g2)


-- Empty Context ------------------------------------------------

data EmptyCtx :: Ctx -> * where
  EmptyNil  :: EmptyCtx '[]
  EmptyCons :: forall x g. EmptyCtx g -> EmptyCtx ('Unused ': g)


-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
-- f1++[(x,t)]++f2 is a frame for g and g'
data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddEHere   :: AddCtx 'Z s '[]            '[ 'Used s ]
  AddHere    :: AddCtx 'Z s ('Unused ': g) ('Used s ': g)
  AddELater  :: AddCtx x s '[] g -> AddCtx ('S x) s '[] ('Unused ': g)
  AddLater   :: AddCtx x s g g'  -> AddCtx ('S x) s (u ': g) (u ': g')


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



singletonAdd :: SingletonCtx x s g -> AddCtx x s '[] g
singletonAdd AddHereS        = AddEHere
singletonAdd (AddLaterS pfS) = AddELater (singletonAdd pfS)

addSingleton :: AddCtx x s '[] g' -> SingletonCtx x s g'
addSingleton AddEHere        = AddHereS
addSingleton (AddELater pfA) = AddLaterS $ addSingleton pfA

addEmptyAbsurd :: AddCtx x s g g'
               -> EmptyCtx g'
               -> a
addEmptyAbsurd (AddELater pfA) (EmptyCons pfE) = addEmptyAbsurd pfA pfE
addEmptyAbsurd (AddLater pfA)  (EmptyCons pfE) = addEmptyAbsurd pfA pfE

-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
-- f1++[(x,s)]++f2 is a frame for g
data SingletonCtx :: Nat -> LType -> Ctx -> * where
  AddHereS  :: SingletonCtx 'Z s '[ 'Used s ]
  AddLaterS :: SingletonCtx x s g
            -> SingletonCtx ('S x) s ('Unused ': g)

addSingletonEmpty :: forall x s g g'. 
                     AddCtx x s g g' 
                  -> SingletonCtx x s g'
                  -> EmptyCtx g
addSingletonEmpty AddHere           AddHereS          = EmptyCons EmptyNil
addSingletonEmpty AddEHere          AddHereS          = EmptyNil
addSingletonEmpty (AddLater pfAdd) (AddLaterS pfSing) = 
                  EmptyCons $ addSingletonEmpty pfAdd pfSing
addSingletonEmpty (AddELater pfAdd) (AddLaterS pfSing) = EmptyNil

singletonInv :: SingletonCtx x s g
             -> SingletonCtx y t g 
             -> Dict ('(x,s) ~ '(y,t))
singletonInv AddHereS AddHereS = Dict
singletonInv (AddLaterS pf1) (AddLaterS pf2) = 
  case singletonInv pf1 pf2 of Dict -> Dict

addSingletonInv :: AddCtx x s g g' 
               -> SingletonCtx y t g' 
               -> Dict ('(x,s) ~ '(y,t))
addSingletonInv AddEHere          AddHereS          = Dict
addSingletonInv AddHere           AddHereS          = Dict
addSingletonInv (AddELater pfAdd) (AddLaterS pfSing) = 
  case addSingletonInv pfAdd pfSing of Dict -> Dict
addSingletonInv (AddLater pfAdd) (AddLaterS pfSing) =
  case addSingletonInv pfAdd pfSing of Dict -> Dict



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

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = 'Unused ': g
  Remove ('S x) (u ': g) = u ': Remove x g


mergeAdd :: Merge g1 g2 g 
         -> AddCtx x s g0 g
         -> Either (AddCtx x s (Remove x g1) g1, Merge (Remove x g1) g2 g0)
                   (AddCtx x s (Remove x g2) g2, Merge g1 (Remove x g2) g0)
mergeAdd = undefined


--- Shifting and Adding

addShift :: AddCtx x s g1 g2
         -> Shift g2' g2
         -> (AddCtx x s (Remove x g2') g2', Shift (Remove x g2') g1)
-- x~0
-- g1=Unused:g0
-- g2=Used s:g0
-- g2'=Used s:g0'
-- pfShift :: Shift g0' g0
-- want: AddCtx 0 s (Unused:g0') (Used s:g0')
-- want: Shift (Unused:g0') (Unused:g0)
addShift AddHere (ShiftLater pfShift) = (AddHere, ShiftLater pfShift)
-- x=0
-- g1=[]
-- g2=[Used s]
-- g2'=Used s:g0'
-- pfShift :: Shift g0' []
-- want: AddCtx 0 s (Unused:g0') (Used s:g0')
-- want: Shift (Unused:g0') []
addShift AddEHere (ShiftLater pfShift) = case pfShift of 
-- x=S y
-- g1=[]
-- g2=Unused:g0
-- pfAdd :: AddCtx y s [] g0
-- g2'=Unused:g0'
-- pfShift :: Shift g0' g0
-- addShift pfAdd pfShift :: (AddCtx y s (Remove y g0') g0', Shift (Remove y g0') [])
-- want: AddCtx (S y) s (Unused:Remove y g0') (Unused:g0')
-- want: Shift (Unused:Remove y g0') []
addShift (AddELater pfAdd) (ShiftLater pfShift) = 
  let (_,pfShift') = addShift pfAdd pfShift in case pfShift' of 
addShift (AddLater pfAdd) (ShiftLater pfShift) = 
  let (pfAdd',pfShift') = addShift pfAdd pfShift in (AddLater pfAdd', ShiftLater pfShift')

addShift2 :: AddCtx x s g1 g2
          -> Shift g2 g3
          -> (AddCtx x s (Remove x g3) g3, Shift g1 (Remove x g3))
addShift2 = undefined
