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


-- Shift -----------------------------------------------------

data Shift :: Nat -> Ctx -> Ctx -> * where
  ShiftHere  :: Shift 'Z g ('Unused ': g)
  ShiftLater :: Shift n g g' -> Shift ('S n) (u ': g) (u ': g')

shiftEmpty :: Shift n g1 g2 -> EmptyCtx g1 -> EmptyCtx g2
shiftEmpty ShiftHere            pfEmpty             = EmptyCons pfEmpty  
shiftEmpty (ShiftLater pfShift) (EmptyCons pfEmpty) = EmptyCons (shiftEmpty pfShift pfEmpty)

unshiftEmpty :: Shift n g1 g2 -> EmptyCtx g2 -> EmptyCtx g1
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

inAdd :: In x s g
      -> AddCtx y t g g'
      -> In x s g'
inAdd InHere        (AddLater _)   = InHere
inAdd (InLater pfI) AddHere        = InLater pfI
inAdd (InLater pfI) (AddLater pfA) = InLater $ inAdd pfI pfA

inAddRemove :: In x s g
            -> AddCtx y t g g'
            -> AddCtx y t (Remove x g) (Remove x g')
inAddRemove InHere        (AddLater pfA) = AddLater pfA
inAddRemove (InLater pfI) AddHere        = AddHere
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


-- Remove ------------------------------------------

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = 'Unused ': g
  Remove ('S x) (u ': g) = u ': Remove x g


emptyRemove :: EmptyCtx g
            -> AddCtx x s g g'
            -> EmptyCtx (Remove x g')
emptyRemove EmptyNil        AddEHere        = EmptyCons EmptyNil
emptyRemove EmptyNil        (AddELater pfA) = EmptyCons $ emptyRemove EmptyNil pfA
emptyRemove pfE             AddHere         = pfE
emptyRemove (EmptyCons pfE) (AddLater pfA)  = EmptyCons $ emptyRemove pfE pfA


-- In -------------------------------

data In :: Nat -> LType -> Ctx -> * where
  InHere  :: In  'Z s ('Used s ': g)
  InLater :: In x s g -> In ('S x) s (u ': g)


addIn :: AddCtx x s g g' -> In x s g'
addIn AddEHere = InHere
addIn AddHere  = InHere
addIn (AddELater pf) = InLater $ addIn pf
addIn (AddLater pf)  = InLater $ addIn pf

inEmptyAbsurd :: In x s g -> EmptyCtx g -> a
inEmptyAbsurd (InLater pfI) (EmptyCons pfE) = inEmptyAbsurd pfI pfE

singletonInInv :: In x s g
               -> SingletonCtx y t g
               -> Dict ('(x,s)~'(y,t))
singletonInInv InHere         AddHereS       = Dict
singletonInInv (InLater pfI) (AddLaterS pfS) = 
  case singletonInInv pfI pfS of Dict -> Dict

inRemove :: In x s g
         -> AddCtx x s (Remove x g) g
inRemove InHere = AddHere 
inRemove (InLater pfIn) = AddLater $ inRemove pfIn

-- Relation between In and Shift

type family InShift x n :: Nat where
  InShift ('S x) 'Z     = x
  InShift 'Z     ('S n) = 'Z
  InShift ('S x) ('S n) = 'S (InShift x n)


inShift :: In x s g
        -> Shift i g' g
        -> In (InShift x i) s g'
inShift (InLater pfI) ShiftHere = pfI
inShift InHere        (ShiftLater pfS) = InHere
inShift (InLater pfI) (ShiftLater pfS) = InLater $ inShift pfI pfS

type family InUnshift x i :: Nat where
  InUnshift x      'Z     = 'S x
  InUnshift 'Z     ('S i) = 'Z
  InUnshift ('S x) ('S i) = 'S (InUnshift x i)

inUnshift :: In x s g
          -> Shift i g g'
          -> In (InUnshift x i) s g'
inUnshift pfI           ShiftHere        = InLater pfI
inUnshift InHere        (ShiftLater pfS) = InHere
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
shiftRemove (ShiftLater pfS) pfI InHere         = ShiftLater pfS
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
unshiftRemove (ShiftLater pfS) InHere        pfI'           = ShiftLater pfS
unshiftRemove (ShiftLater pfS) (InLater pfI) (InLater pfI') = 
    ShiftLater $ unshiftRemove pfS pfI pfI'


-- Relation between In and Merge

mergeInSplit :: Merge g1 g2 g
             -> In x s g
             -> Either (In x s g1) (In x s g2)
mergeInSplit MergeEL      InHere = Right InHere
mergeInSplit MergeER      InHere = Left  InHere
mergeInSplit (MergeL pfM) InHere = Left InHere
mergeInSplit (MergeR pfM) InHere = Right InHere
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
mergeIn1 (MergeL pfM) InHere InHere = MergeU pfM
mergeIn1 (MergeL pfM) (InLater pfI1) (InLater pfI3) = MergeL $ mergeIn1 pfM pfI1 pfI3
mergeIn1 (MergeR pfM) (InLater pfI1) (InLater pfI3) = MergeR $ mergeIn1 pfM pfI1 pfI3
mergeIn1 (MergeU pfM) (InLater pfI1) (InLater pfI3) = MergeU $ mergeIn1 pfM pfI1 pfI3

mergeIn2 :: Merge g1 g2 g3
         -> In x s g2
         -> In x s g3
         -> Merge g1 (Remove x g2) (Remove x g3)
mergeIn2 MergeEL _ _ = MergeEL
mergeIn2 (MergeR pfM) InHere InHere = MergeU pfM
mergeIn2 (MergeL pfM) (InLater pfI2) (InLater pfI3) = MergeL $ mergeIn2 pfM pfI2 pfI3
mergeIn2 (MergeR pfM) (InLater pfI2) (InLater pfI3) = MergeR $ mergeIn2 pfM pfI2 pfI3
mergeIn2 (MergeU pfM) (InLater pfI2) (InLater pfI3) = MergeU $ mergeIn2 pfM pfI2 pfI3



{-
addTwiceEquiv :: AddCtx x s g1 g
              -> AddCtx x s g2 g
              -> Equiv g1 g2
addTwiceEquiv = undefined


mergeER :: Equiv g g'
        -> Merge g '[] g'
mergeER = undefined
mergeEL :: Equiv g g'
        -> Merge '[] g g'
mergeEL = undefined

mergeAdd1Help :: g1' ~ Remove x (Used t:g1)
              => Merge g1 g2 g3
              -> AddCtx x s g1' (Used t:g1)
              -> AddCtx x s g3' (Used t:g3)
              -> Merge g1' ('Unused ': g2) g3'
-- g1'=Unused:g1
-- g3'=[]
mergeAdd1Help pfM AddHere AddEHere = undefined

mergeAdd1 :: g1' ~ Remove x g1 => Merge g1 g2 g3
          -> AddCtx x s g1' g1
          -> AddCtx x s g3' g3
          -> Merge g1' g2 g3'
mergeAdd1 MergeER      pfA1 pfA3 = mergeER $ addTwiceEquiv pfA1 pfA3
-- g1=Used t:g1''
-- g2='Unused:g2''
-- g3=Used t:g3''
-- pfM :: Merge g1'' g2'' g3''
-- pfA1 :: AddCtx x s g1' (Used t:g1'')
-- pfA2 :: AddCtx x s g3' (Used t:g3'')
-- want: Merge g1' (Unused:g2'') g3'
mergeAdd1 (MergeL pfM) pfA1 pfA3 = mergeAdd1Help pfM pfA1 pfA3
mergeAdd1 _ _ _ = undefined

mergeAdd2 :: Merge g1 g2 g3
          -> AddCtx x s g2' g2
          -> AddCtx x s g3' g3
          -> Merge g1 g2' g3'
mergeAdd2 = undefined

-- I'm not sure we can really get Merge _ _ g0;
-- what if g0 is []??
-- we really want Merge (Remove x g1) g2 (Remove x g3)
mergeAdd :: Merge g1 g2 g 
         -> AddCtx x s g0 g
         -> Either (AddCtx x s (Remove x g1) g1, Merge (Remove x g1) g2 g0)
                   (AddCtx x s (Remove x g2) g2, Merge g1 (Remove x g2) g0)
mergeAdd pfM pfA = case mergeInSplit pfM (addIn pfA) of 
  Left  pfI -> Left  (inRemove pfI, mergeAdd1 pfM (inRemove pfI) pfA)
  Right pfI -> Right (inRemove pfI, mergeAdd2 pfM (inRemove pfI) pfA)

mergeAddRemove :: Merge g1 g2 g 
         -> AddCtx x s g0 g
         -> Either (AddCtx x s (Remove x g1) g1, Merge (Remove x g1) g2 (Remove x g))
                   (AddCtx x s (Remove x g2) g2, Merge g1 (Remove x g2) (Remove x g))
mergeAddRemove = undefined

-}


--- Shifting and Adding

-- no because the index might not be the same
{-
inShiftRemove :: In x s g
              -> Shift g' g
              -> Shift g' (Remove x g)
inShiftRemove InHere       (ShiftLater pfS) = undefined




inUnshift :: In x s g
          -> Shift g g'
          -> In x s g'
inUnshift = undefined

inUnshiftRemove :: In x s g
                -> Shift g g'
                -> Shift (Remove x g) (Remove x g')
inUnshiftRemove = undefined
-}
{-
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
-}
