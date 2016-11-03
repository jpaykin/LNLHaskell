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
import Lang 

-- Substitution ----------------------------------------

subst :: In x s g
      -> LExp '[] s
      -> LExp g t
      -> LExp (Remove x g) t
subst pfI s (Var pfS)                    = substVar     pfI s pfS
subst pfI s (Abs pfA e')                 = substAbs     pfI s pfA e'
subst pfI s (App pfM e1 e2)              = substApp     pfI s pfM e1 e2
subst pfI s (Pair pfM e1 e2)             = substPair    pfI s pfM e1 e2
subst pfI s (LetPair pfM pfA pfA' e1 e2) = substLetPair pfI s pfM pfA pfA' e1 e2
subst pfI s (Put pfE a)                  = substPut     pfI s pfE a
subst pfI s (LetBang pfM e f)            = substLetBang pfI s pfM e f
subst pfI s (Shift pfS e)                = substShift   pfI s pfS e
subst pfI s (Unshift pfS e)              = substUnshift pfI s pfS e


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
    Left  pfI1 -> App (mergeIn1 pfM pfI1 pfI) (subst pfI1 s e1) e2
    Right pfI2 -> App (mergeIn2 pfM pfI2 pfI) e1 (subst pfI2 s e2)

substPair :: In x s g
          -> LExp '[] s
          -> Merge g1 g2 g
          -> LExp g1 t1
          -> LExp g2 t2
          -> LExp (Remove x g) (t1 ⊗ t2)
substPair pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> Pair (mergeIn1 pfM pfI1 pfI) (subst pfI1 s e1) e2
    Right pfI2 -> Pair (mergeIn2 pfM pfI2 pfI) e1 (subst pfI2 s e2)

substLetPair :: forall x s t g1 g2 g x1 x2 s1 s2 g2' g2''.
                In x s g
             -> LExp '[] s
             -> Merge g1 g2 g
             -> AddCtx x1 s1 g2 g2'
             -> AddCtx x2 s2 g2' g2''
             -> LExp g1 (s1 ⊗ s2)
             -> LExp g2'' t
             -> LExp (Remove x g) t
substLetPair pfI s pfM pfA1 pfA2 e e' =
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetPair (mergeIn1 pfM pfI1 pfI) pfA1 pfA2 (subst pfI1 s e) e'
    Right pfI2 -> LetPair pfM' pfA1' pfA2' e e''
      where
     -- pfI2 :: In x s g2
        pfI2' :: In x s g2'
        pfI2' = inAdd pfI2 pfA1
        pfI2'' :: In x s g2''
        pfI2'' = inAdd pfI2' pfA2
        pfM' :: Merge g1 (Remove x g2) (Remove x g)
        pfM' = mergeIn2 pfM pfI2 pfI
        pfA1' :: AddCtx x1 s1 (Remove x g2) (Remove x g2')
        pfA1' = inAddRemove pfI2 pfA1
        pfA2' :: AddCtx x2 s2 (Remove x g2') (Remove x g2'')
        pfA2' = inAddRemove pfI2' pfA2
        e'' :: LExp (Remove x g2'') t
        e'' = subst pfI2'' s e'


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
    Left  pfI1 -> LetBang (mergeIn1 pfM pfI1 pfI) (subst pfI1 s e) f
    Right pfI2 -> LetBang (mergeIn2 pfM pfI2 pfI) e (\x -> subst pfI2 s (f x))

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
eval' pfE (Pair pfM e1 e2)              = VPair (eval' pfE1 e1) (eval' pfE2 e2)
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE
eval' pfE (LetPair pfM pfA1 pfA2 e1 e2) = evalPair pfE pfM pfA1 pfA2 e1 e2
eval' pfE             (Shift pfS e)     = eval' (unshiftEmpty pfS pfE) e
eval' pfE             (Unshift pfS e)   = eval' (shiftEmpty pfS pfE) e


evalPair :: forall g g1 g2 x1 x2 t1 t2 g2' g2'' r. 
            EmptyCtx g 
         -> Merge g1 g2 g
         -> AddCtx x1 t1 g2 g2'
         -> AddCtx x2 t2 g2' g2''
         -> LExp g1 (t1 ⊗ t2)
         -> LExp g2'' r
         -> LVal r
evalPair pfE pfM pfA1 pfA2 e1 e2 = 
  case eval' pfE1 e1 of 
    VPair v1 v2 -> eval' pfE2' e2''
      where
        e2' :: LExp (Remove x2 g2'') r
        e2' = substVal pfI2 v2 e2
        e2'' :: LExp (Remove x1 (Remove x2 g2'')) r
        e2'' = substVal pfI1' v1 e2'
  where
    (pfE1,pfE2) = mergeEmpty pfM pfE
    pfI1 :: In x1 t1 g2'
    pfI1 = addIn pfA1
    pfI1' :: In x1 t1 (Remove x2 g2'')
    pfI1' = equivIn pfI1 pfEq2
    pfI2 :: In x2 t2 g2''
    pfI2 = addIn pfA2
    pfEq2 :: Equiv g2' (Remove x2 g2'')
    pfEq2 = addRemoveEquiv pfA2
    pfEq2' :: Equiv (Remove x1 g2') (Remove x1 (Remove x2 g2''))
    pfEq2' = equivRemove pfI1 pfEq2
    pfEq1 :: Equiv g2 (Remove x1 g2')
    pfEq1 = addRemoveEquiv pfA1
    pfEq :: Equiv g2 (Remove x1 (Remove x2 g2''))
    pfEq = equivTrans pfEq1 pfEq2'
    pfE2' :: EmptyCtx (Remove x1 (Remove x2 g2''))
    pfE2' = equivEmpty pfE2 pfEq


    

eval :: EmptyCtx g -> LExp g s -> LExp '[] s
eval pfE e = valToExp $ eval' pfE e
