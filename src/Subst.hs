{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, LambdaCase,
             EmptyCase
#-}

module Subst where

import Data.Kind
import Data.Constraint

import Types
import Context
import Proofs
import Lang hiding (subst, eval', eval)

-- Substitution ----------------------------------------

subst :: In x s g
      -> LExp '[] s
      -> LExp g t
      -> LExp (Remove x g) t
subst pfI s (Var pfS)           = substVar     pfI s pfS
subst pfI s (Abs pfA e')        = substAbs     pfI s pfA e'
subst pfI s (App pfM e1 e2)     = substApp     pfI s pfM e1 e2
subst pfI s Unit                = substUnit    pfI
subst pfI s (LetUnit pfM e1 e2) = substLetUnit pfI s pfM e1 e2
subst pfI s (Pair pfM e1 e2)    = substPair    pfI s pfM e1 e2
subst pfI s (LetPair pfM pfAx pfAy e1 e2) 
                                = substLetPair pfI s pfM pfAx pfAy e1 e2
subst pfI s (ETuple es)         = substTuple   pfI s es
subst pfI s (Case pfM pfA e1 e2)= substCase    pfI s pfM pfA e1 e2
subst pfI s (Put pfE a)         = substPut     pfI s pfE a
subst pfI s (LetBang pfM e f)   = substLetBang pfI s pfM e f
subst pfI s (Shift pfS e)       = substShift   pfI s pfS e
subst pfI s (Unshift pfS e)     = substUnshift pfI s pfS e

substTuple' :: In x s g 
            -> LExp '[] s
            -> LExps g ts
            -> LExps (Remove x g) ts
substTuple' pfI s LExpNil = case pfI of 
substTuple' pfI s (LExpCons pfM e es) = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LExpCons pfM' (subst pfI1 s e) es
      where
        pfM' = mergeIn1 pfM pfI1
    Right pfI2 -> LExpCons pfM' e (substTuple' pfI2 s es)
      where
        pfM' = mergeIn2 pfM pfI2


substTuple :: In x s g -> LExp '[] s -> LExps g ts
           -> LExp (Remove x g) (Tuple ts)
substTuple pfI s es = ETuple $ substTuple' pfI s es


substPat :: InPat p s g
         -> LVal s 
         -> LExp g t
         -> LExp (RemovePat p g) t
substPat (InVar pfI) s t = subst pfI (valToExp s) t
substPat (InTuple pfIs) (VTuple vs) t = substPats pfIs vs t

substPats :: InPats ps ts g 
          -> LVals ts
          -> LExp g t
          -> LExp (RemovePats ps g) t
substPats InNil VNil e = e
substPats (InCons pfM pfI pfIs) (VCons v vs) e = substPat pfI' v $ substPats pfIs' vs e
  where
--  pfIs' :: InPats ps ts g
    pfIs' = inPatsMerge2 pfM pfIs
--  pfI'  :: InPat p s (RemovePats ps g)
    pfI'  = inPatMerge1 pfM' pfI
--  pfM' :: Merge g1 (RemovePats ps g2) (RemovePats ps g) 
    pfM' = mergeInPats2 pfM pfIs



substVal :: In x s g -> LVal s -> LExp g t -> LExp (Remove x g) t
substVal pfI v e = subst pfI (valToExp v) e

substVar :: In x s g
         -> LExp '[] s
         -> SingletonCtx y t g
         -> LExp (Remove x g) t
substVar pfI s pfS = case singletonInInv pfI pfS of Dict -> transportUp pfE s
  where
    pfE = singletonEmpty pfS

substAbs :: In x s g
         -> LExp '[] s
         -> AddCtx y t1 g g'
         -> LExp g' t2
         -> LExp (Remove x g) (t1 ⊸ t2)
substAbs pfI s pfA e = Abs pfA' $ subst pfI' s e
  where
 -- pfI' :: In x s g'
    pfI' = inAdd pfI pfA
 -- e'   :: LExp (Remove x g') t2
    e'   = subst pfI' s e
 -- pfA' :: AddCtx y t (Remove x g) (Remove x g')
    pfA' = inAddRemove pfI pfA


substApp  :: In x s g 
          -> LExp '[] s
          -> Merge g1 g2 g
          -> LExp g1 (t1 ⊸ t2)
          -> LExp g2 t1
          -> LExp (Remove x g) t2
substApp pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> App (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> App (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substUnit :: In x s '[] -> a
substUnit = \case


substLetUnit :: In x s g 
             -> LExp '[] s
             -> Merge g1 g2 g
             -> LExp g1 One
             -> LExp g2 t
             -> LExp (Remove x g) t
substLetUnit pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetUnit (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> LetUnit (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substPair :: In x s g 
          -> LExp '[] s
          -> Merge g1 g2 g
          -> LExp g1 t1
          -> LExp g2 t2
          -> LExp (Remove x g) (t1 ⊗ t2)
substPair pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> Pair (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> Pair (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substLetPair :: In x s g
             -> LExp '[] s
             -> Merge g1 g2 g
             -> AddCtx y1 t1 g2  g2'
             -> AddCtx y2 t2 g2' g2''
             -> LExp g1 (t1 ⊗ t2)
             -> LExp g2'' r
             -> LExp (Remove x g) r
substLetPair pfI s pfM pfA1 pfA2 e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetPair (mergeIn1 pfM pfI1) pfA1 pfA2 (subst pfI1 s e1) e2
    -- pfI2   :: In x s g2
    -- pfI2'  :: In x s g2'
    -- pfI2'' :: In x s g2''
    -- pfM'   :: Merge g1 (Remove x g2) (Remove x g)
    -- pfA1'  :: AddCtx y1 t1 (Remove x g2)  (Remove x g2')
    -- pfA2'  :: AddCtx y2 t2 (Remove x g2') (Remove x g2'')
    Right pfI2 -> LetPair pfM' pfA1' pfA2' e1 e2'
      where
        pfI2'  = inAdd pfI2  pfA1
        pfI2'' = inAdd pfI2' pfA2
        e2'    = subst pfI2'' s e2
        pfM'   = mergeIn2 pfM pfI2
        pfA1'  = inAddRemove pfI2  pfA1
        pfA2'  = inAddRemove pfI2' pfA2

substCase :: forall x p s t r g g1 g2 g2'.
             In x s g 
          -> LExp '[] s
          -> Merge g1 g2 g
          -> AddPat p t g2 g2'
          -> LExp g1 t
          -> LExp g2' r
          -> LExp (Remove x g) r
substCase pfI s pfM pfA e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> Case (mergeIn1 pfM pfI1) pfA (subst pfI1 s e1) e2
    Right pfI2 -> Case pfM' pfA' e1 (subst pfI2' s e2)
      where
        pfI2' :: In x s g2'
        pfI2' = inAddPatIn pfI2 pfA
        pfM'  :: Merge g1 (Remove x g2) (Remove x g)
        pfM' = mergeIn2 pfM pfI2
        pfA'  :: AddPat p t (Remove x g2) (Remove x g2')
        pfA'  = inAddPatRemove pfI2 pfA



substPut :: In x s g
         -> LExp '[] s
         -> EmptyCtx g
         -> a
         -> LExp (Remove x g) (Lower a)
substPut pfI _ pfE _ = inEmptyAbsurd pfI pfE

substLetBang :: In x s g
             -> LExp '[] s
             -> Merge g1 g2 g
             -> LExp g1 (Lower a)
             -> (a -> LExp g2 t)
             -> LExp (Remove x g) t
substLetBang pfI s pfM e f = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetBang (mergeIn1 pfM pfI1) (subst pfI1 s e) f
    Right pfI2 -> LetBang (mergeIn2 pfM pfI2) e (\x -> subst pfI2 s (f x))

substShift :: In x s g
           -> LExp '[] s
           -> Shift i g' g
           -> LExp g' t
           -> LExp (Remove x g) t
substShift pfI s pfS e = Shift pfS' $ subst pfI' s e
  where
    e'   = subst pfI' s e
    pfI' = inShift pfI pfS
    pfS' = shiftRemove pfS pfI' pfI


substUnshift :: In x s g
             -> LExp '[] s
             -> Shift i g g'
             -> LExp g' t
             -> LExp (Remove x g) t
substUnshift pfI s pfS e = Unshift pfS' $ subst pfI' s e
  where
    pfI' = inUnshift pfI pfS
    pfS' = unshiftRemove pfS pfI pfI'


-- Evaluation --------------------------------------------

eval' :: EmptyCtx g -> LExp g s -> LVal s
eval' pfE (Abs pfAdd e)       = VAbs pfE pfAdd e
eval' pfE (App pfMerge e1 e2) = 
  case (eval' pfE1 e1, eval pfE2 e2) of
    (VAbs pfE pfA e1', e2') -> eval' EmptyNil e'
      where
        e' = transportDown (emptyRemove pfE pfA) $ subst (addIn pfA) e2' e1'
  where
    (pfE1,pfE2)  = mergeEmpty pfMerge pfE
eval' pfE Unit       = VUnit
eval' pfE (LetUnit pfM e1 e2) = 
  case (eval' pfE1 e1, eval' pfE2 e2) of
    (VUnit, v2) -> v2
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE
eval' pfE (Pair pfM e1 e2) = VPair (eval' pfE1 e1) (eval' pfE2 e2)
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE

-- pfE  :: EmptyCtx g
-- pfE1 :: EmptyCtx g1
-- pfE2 :: EmptyCtx g2
-- pfM  :: Merge g1 g2 g
-- pfA1 :: AddCtx y1 t1 g2  g2'
-- pfI1 :: In y1 g2'
-- pfI1':: In y1 g2''
-- pfA2 :: AddCtx y2 t2 g2' g2''
-- pfA2':: AddCtx y2 t2 (Remove y1 g2') (Remove y2 g2'')
-- pfI2 :: In y2 g2''
-- pfI2'=addIn pfA2' :: In y2 (Remove x1 g2'')
-- e1   :: LExp g1 (t1 ⊗ t2)
-- e2   :: LExp g2'' r
-- e2'  :: LExp (Remove y1 g2'') r
-- e2'' :: LExp (Remove y2 (Remove y1 g2'')) r
-- pfA2':: AddCtx y2 t2 (Remove y1 g2') (Remove y1 g2'')
-- e12' = addEquivRemove pfA2'  :: Equiv (Remove y1 g2') (Remove y2 (Remove y1 g2''))
-- pfA1  :: AddCtx y1 t1 g2 g2'
-- eq2 = addEquivRemove pfA1 :: Equiv g2 (Remove y1 g2')
-- eq2'' = equivTrans eq2 eq2' :: Equiv g2 (Remove y2 (Remove y1 g2''))
-- pfE2'' = equivEmpty pfE2 e2'' :: EmptyCtx (Remove y2 (Remove y1 g2''))


-- _ :: AddCtx y1 t1 _ (Remove y2 g2'')
-- pfA2' = inAddRemove pfI1 pfA2' :: AddCtx y2 t2 (Remove y1 g2') (Remove y2 g2')


-- want :: LVal r
eval' pfE (LetPair pfM pfA1 pfA2 e1 e2) = 
  case eval' pfE1 e1 of
    VPair v1 v2 -> eval' pfE2'' e2''
      where
        e2'  = substVal pfI1' v1 e2
        e2'' = substVal pfI2' v2 e2'
        pfE2'' = equivEmpty pfE2 eq2''
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE
    pfI1        = addIn pfA1
    pfI1'       = inAdd pfI1 pfA2
    pfI2        = addIn pfA2
    pfI2'       = addIn pfA2'
    pfA2'       = inAddRemove pfI1 pfA2
    eq2         = addEquivRemove pfA1
    eq2'        = addEquivRemove pfA2' 
    eq2''       = equivTrans eq2 eq2'

eval' pfE (ETuple es) = VTuple $ evalTuple pfE es
eval' pfE (Case pfM pfA e1 e2) = evalCase pfE pfM pfA e1 e2


eval' pfE (Put pf a) = VPut a
eval' pfE (LetBang pfMerge e k) = 
  eval' EmptyNil $ transportDown pfE2 (k a)
  where
    (pfE1,pfE2) = mergeEmpty pfMerge pfE
    a                   = fromVPut $ eval' pfE1 e

-- pfE :: EmptyCtx g2
-- pfS :: Shift g1 g2
-- e   :: LExp g1 t
-- (Shift pfS e) :: LExp g2 s
eval' pfE             (Shift pfS e)   = eval' (unshiftEmpty pfS pfE) e
-- pfE :: EmptyCtx g1
-- pfS :: Shift g1 g2
-- e   :: LExp g2 t
-- (Unshift pfS e) :: LExp g1 s
eval' pfE             (Unshift pfS e) = eval' (shiftEmpty pfS pfE) e



evalCase :: EmptyCtx g 
         -> Merge g1 g2 g 
         -> AddPat p s g2 g2' 
         -> LExp g1 s
         -> LExp g2' t
         -> LVal t
evalCase pfE pfM pfA e1 e2 = 
  case eval' pfE1 e1 of { v1 -> 
    eval' pfE2' $ substPat (addInPat pfA) v1 e2
  }
  where
  -- pfE1 :: EmptyCtx g1
  -- pfE2 :: EmptyCtx g2
    (pfE1,pfE2) = mergeEmpty pfM pfE
 -- pfE2' :: EmptyCtx (RemovePat p g2')
    pfE2' = emptyRemovePat pfE2 pfA


evalTuple :: EmptyCtx g
          -> LExps g ts
          -> LVals ts
evalTuple pfE LExpNil = VNil
evalTuple pfE (LExpCons pfM e es) = VCons (eval' pfE1 e) (evalTuple pfE2 es)
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE

eval :: EmptyCtx g -> LExp g s -> LExp '[] s
eval pfE e = valToExp $ eval' pfE e
