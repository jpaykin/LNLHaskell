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

inSCtxRemove :: InN x s g -> SNCtx g -> SCtx (RemoveN x g)
inSCtxRemove InEnd            SEnd        = SEmpty
inSCtxRemove (InHere _)      (SCons u g') = SN $ SCons SUnused g'
inSCtxRemove (InLater _ pfI) (SCons u g') = consN u $ inSCtxRemove pfI g'


sCtxNAddN :: SNCtx g -> AddNCtxN x s g g' -> SNCtx g'
sCtxNAddN (SCons _ g) (AddHere _)      = SCons SUsed g
sCtxNAddN SEnd        (AddEnd pfS)     = SCons SUsed $ singletonSCtxN pfS
sCtxNAddN (SCons u g) (AddLater _ pfA) = SCons u $ sCtxNAddN g pfA

sCtxAddN :: SCtx g -> AddCtxN x s g g' -> SNCtx g'
sCtxAddN g      AddEHere        = SEnd
sCtxAddN g      (AddELater pfA) = SCons SUnused $ sCtxAddN g pfA
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


-- Freshness ---------------------------------------------

knownFresh :: SCtx g -> SIdent (Fresh g)
knownFresh SEmpty = SZ
knownFresh (SN SEnd) = SS SZ
knownFresh (SN (SCons SUnused _)) = SZ
knownFresh (SN (SCons SUsed   g)) = SS $ knownFresh (SN g)


freshDisjoint :: SCtx g -> Disjoint (Fresh g) (Fresh2 g)
freshDisjoint SEmpty = DisjointZS
freshDisjoint (SN SEnd) = DisjointSS $ DisjointZS
freshDisjoint (SN (SCons SUnused _)) = DisjointZS
freshDisjoint (SN (SCons SUsed   g)) = DisjointSS $ freshDisjoint (SN g)


-- Disjointness --------------------------------------------

disjointRemoveN :: Disjoint x y -> InN x s g -> InN y t g -> In x s (RemoveN y g)
disjointRemoveN DisjointZS       (InHere g)       (InLater _ pfI)  = 
  case inSCtxRemove pfI g of 
    SEmpty -> In $ InEnd
    SN g'  -> In $ InHere g'
disjointRemoveN DisjointSZ       (InLater _ pfI)  (InHere g)     = In $ InLater SUnused pfI
disjointRemoveN (DisjointSS pfD) (InLater u pfI1) (InLater _ pfI2) = 
  case disjointRemoveN pfD pfI1 pfI2 of In pfI -> In (InLater u pfI)

-- Shift ---------------------------------------------------

-- shiftSCtxN :: ShiftN i g g' -> SNCtx g -> SNCtx g'
-- shiftSCtxN ShiftHere g = SCons SUnused g
-- shiftSCtxN (ShiftLater pfS) 

-- shiftSCtx :: Shift i g g' ->  SCtx g -> SCtx g'
-- shiftSCtx (Shift ShiftHere)         g = SCons SUnused g
-- shiftSCtx (Shift (ShiftLater pfSh)) (SCons u g) = SCons u $ shiftSCtx pfSh g

-- unshiftSCtx :: Shift i g g' -> SCtx g' -> SCtx g
-- unshiftSCtx ShiftHere (SCons SUnused g0') = g0'
-- unshiftSCtx (ShiftLater pfS) (SCons u g0') = SCons u $ unshiftSCtx pfS g0'


-- Empty Context ----------------------------------------------

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
inNAddRemoveLaterN InEnd          (AddEnd pfS)     = AddN $ AddELater $ singletonAddN pfS
inNAddRemoveLaterN (InHere g)     (AddLater u pfS) = AddN . AddNN . AddLater SUnused $ pfS
inNAddRemoveLaterN (InLater _ pfI)  (AddHere g0)   = 
  case inSCtxRemove pfI g0 of
    SEmpty -> AddN AddEHere
    SN g'  -> AddN . AddNN . AddHere $ g'

singletonAddN :: SingletonNCtx x s g -> AddCtxN x s 'Empty g
singletonAddN AddHereS        = AddEHere
singletonAddN (AddLaterS pfS) = AddELater $ singletonAddN pfS

singletonAdd :: SingletonCtx x s g -> AddCtx x s 'Empty g
singletonAdd (SingN pfS) = AddN $ singletonAddN pfS

addSingleton :: AddCtx x s 'Empty g -> SingletonCtx x s g
addSingleton (AddN pfA) = SingN $ addNSingleton pfA

addNSingleton :: AddCtxN x s 'Empty g -> SingletonNCtx x s g
addNSingleton AddEHere = AddHereS
addNSingleton (AddELater pfA) = AddLaterS $ addNSingleton pfA

-- previously called addFAdd
addFresh :: SCtx g -> AddCtx (Fresh g) s g (Add (Fresh g) s g)
addFresh g = AddN $ addFreshN g

addFreshN :: SCtx g -> AddCtxN (Fresh g) s g (AddN (Fresh g) s g)
addFreshN SEmpty = AddEHere
addFreshN (SN g) = AddNN $ addNFreshN g

addNFreshN :: SNCtx g -> AddNCtxN (FreshN g) s g (AddNN (FreshN g) s g)
addNFreshN SEnd              = AddEnd $ singletonNFresh $ SZ
addNFreshN (SCons SUnused g) = AddHere g
addNFreshN (SCons SUsed   g) = AddLater SUsed $ addNFreshN g

-- Singleton Context ------------------------------------------


-- previously called fSingletonCtx
singletonFresh :: SIdent x -> SingletonCtx x s (Singleton x s)
singletonFresh x = SingN $ singletonNFresh x

singletonNFresh :: SIdent x -> SingletonNCtx x s (SingletonN x s)
singletonNFresh SZ     = AddHereS
singletonNFresh (SS x) = AddLaterS $ singletonNFresh x


-- Merge ----------------------------------------------------

-- Remove ------------------------------------------

singletonRemove :: SingletonCtx x s g -> RemoveCtx x g g' -> Dict (g' ~ 'Empty)
singletonRemove = undefined

removeAdd :: RemoveCtx x g g' -> AddCtx y t g g0 -> (RemoveCtx x g0 (Remove x g0), AddCtx y t g' (Remove x g0))
removeAdd = undefined

inRemove :: In x s g -> RemoveCtx x g (Remove x g)
inRemove = undefined

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
addInN AddEHere        = InEnd
addInN (AddELater pfE) = InLater SUnused $ addInN pfE
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
inAddRemoveN InEnd           = AddEHere
inAddRemoveN (InHere g)      = AddNN $ AddHere g
inAddRemoveN (InLater u pfI) = addConsN u z $ inAddRemoveN pfI 
  where
    z = inSCtxRemove pfI $ inSNCtx pfI

inAddRemove :: In x s g -> AddCtx x s (Remove x g) g
inAddRemove (In pfI) = AddN $ inAddRemoveN pfI

addConsN :: SUsage u -> SCtx g -> AddCtxN x s g g' -> AddCtxN ('S x) s (ConsN u g) ('Cons u g')
addConsN SUsed   SEmpty    pfA         = AddNN . AddEnd $ addNSingleton pfA
addConsN SUnused SEmpty    pfA         = AddELater pfA
addConsN u       (SN g)    (AddNN pfA) = AddNN $ AddLater u pfA




{-

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

-}

-- Relation between In and Merge

mergeSUsage :: MergeU g1 g2 g3 -> (SUsage g1, SUsage g2, SUsage g3)
mergeSUsage MergeUn = (SUnused, SUnused, SUnused)
mergeSUsage MergeUL = (SUsed,   SUnused, SUsed)
mergeSUsage MergeUR = (SUnused, SUsed,   SUsed)

mergeSNCtx :: MergeN g1 g2 g -> SNCtx g -> (SNCtx g1, SNCtx g2)
mergeSNCtx MergeEndL (SCons SUsed g) = (SEnd, SCons SUnused g)
mergeSNCtx MergeEndR (SCons SUsed g) = (SCons SUnused g, SEnd)
mergeSNCtx (MergeCons pfU pfM) (SCons _ g) = 
  let (u1,u2,u) = mergeSUsage pfU 
      (g1,g2)   = mergeSNCtx pfM g
  in (SCons u1 g1, SCons u2 g2)

mergeNInSplit :: MergeN g1 g2 g -> InN x s g -> Either (InN x s g1) (InN x s g2)
mergeNInSplit MergeEndL           (InHere _)      = Left  InEnd
mergeNInSplit MergeEndL           (InLater _ pfI) = Right (InLater SUnused pfI)
mergeNInSplit MergeEndR           (InHere _)      = Right InEnd
mergeNInSplit MergeEndR           (InLater _ pfI) = Left  (InLater SUnused pfI)
mergeNInSplit (MergeCons pfU pfM) (InHere g)      = 
  let (g1,g2) = mergeSNCtx pfM g 
  in case pfU of
    MergeUL -> Left  $ InHere g1
    MergeUR -> Right $ InHere g2
mergeNInSplit (MergeCons pfU pfM) (InLater u pfI) =  
  let (u1,u2,u3) = mergeSUsage pfU 
  in case mergeNInSplit pfM pfI of
    Left  pfI1 -> Left  $ InLater u1 pfI1
    Right pfI2 -> Right $ InLater u2 pfI2

mergeInSplit :: Merge g1 g2 g -> In x s g -> Either (In x s g1) (In x s g2)
mergeInSplit MergeEL pfI = Right pfI
mergeInSplit MergeER pfI = Left  pfI
mergeInSplit (MergeN pfM) (In pfI) = 
  case mergeNInSplit pfM pfI of
    Left  pfI1 -> Left  $ In pfI1
    Right pfI2 -> Right $ In pfI2

mergeNIn1 :: MergeN g1 g2 g3 -> InN x s g1 -> InN x s g3 
          -> Merge (RemoveN x g1) ('N g2) (RemoveN x g3)
mergeNIn1 MergeEndL               InEnd            (InHere _)       = MergeEL
mergeNIn1 MergeEndR               (InLater _ pfI1) (InLater _ pfI3) = undefined 
mergeNIn1 (MergeCons MergeUL pfM) (InHere _)       (InHere _)       = 
    MergeN $ MergeCons MergeUn pfM
mergeNIn1 (MergeCons pfU pfM)     (InLater _ pfI1) (InLater _ pfI3) = undefined
--    MergeN $ MergeCons pfU $ mergeNIn1 pfM pfI1 pfI3

mergeIn1 :: Merge g1 g2 g3 -> In x s g1 -> In x s g3 -> Merge (Remove x g1) g2 (Remove x g3)
mergeIn1 MergeER _ _ = undefined -- MergeER
mergeIn1 (MergeN pfM) (In pfI1) (In pfI2) = mergeNIn1 pfM pfI1 pfI2

mergeIn2 :: Merge g1 g2 g3 -> In x s g2 -> In x s g3 -> Merge g1 (Remove x g2) (Remove x g3) 
mergeIn2 = undefined

mergeEmpty :: Merge g1 g2 'Empty -> Dict (g1 ~ 'Empty, g2 ~ 'Empty)
mergeEmpty = undefined

{-


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



-}

-- Div -------------------------------------------------------

divMerge :: Div g3 g2 g1 -> Merge g1 g2 g3
divMerge = undefined

divSymm :: Div g3 g2 g1 -> Div g3 g1 g2
divSymm = undefined
