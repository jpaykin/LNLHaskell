{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase
#-}

module Subst where

import Data.Kind
import Data.Constraint

import Types
import Context
import Lang hiding (subst, eval', eval)

-- Substitution ----------------------------------------

subst :: In x s g
      -> LExp '[] s
      -> LExp g t
      -> LExp (Remove x g) t
subst pfI s (Var pfS)         = substVar     pfI s pfS
subst pfI s (Abs pfA e')      = substAbs     pfI s pfA e'
subst pfI s (App pfM e1 e2)   = substApp     pfI s pfM e1 e2
subst pfI s (Put pfE a)       = substPut     pfI s pfE a
subst pfI s (LetBang pfM e f) = substLetBang pfI s pfM e f
subst pfI s (Shift pfS e)     = substShift   pfI s pfS e
subst pfI s (Unshift pfS e)   = substUnshift pfI s pfS e

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
substAbs = undefined


substApp  :: In x s g 
          -> LExp '[] s
          -> Merge g1 g2 g
          -> LExp g1 (t1 ⊸ t2)
          -> LExp g2 t1
          -> LExp (Remove x g) t2
substApp = undefined

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
substLetBang = undefined

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

{-
-- g=(Used s : g0)
-- want: LExp (Unused : g0) t
-- g'=(Used s : g0')
-- pfS :: Shift g0' g0
-- e :: LExp (Used s : g0') t
substShift InHere s (ShiftLater pfS) e = Shift pfS' e'
  where
--  e' :: LExp (Unused : g0')
    e' = subst InHere s e
--  pfS' :: Shift (Unused : g0') (Unused : g0)
    pfS' = ShiftLater pfS

-- g=u:g'
-- x=S y
-- pfI :: In y s g'
-- want: LExp (u:Remove y g') t
-- e :: LExp g' t
-- subst y s pfI e :: LExp (Remove y g') t
substShift (InLater pfI) s ShiftHere        e = Shift ShiftHere $ subst pfI s e

-- g=u:g0
-- s=S y
-- pfI :: In y s g0
-- g'=u:g0'
-- pfS :: Shift g0' g0
-- e :: LExp (u:g0') t
-- want: LExp (u:Remove y g0) t
-- substShift pfI s pfS :: LExp g0' t -> LExp (Remove y g0) t
substShift (InLater pfI) s (ShiftLater pfS) e = Shift pfS'' e'
  where
 -- pfI' :: Shift (InShift y i) s g0'
    pfI' = inShift pfI pfS
 -- e' :: LExp (u:Remove y g0') t
    e' = subst (InLater pfI') s e
 -- pfS' :: Shift (Remove y g0') (Remove y g0)
    pfS' = shiftRemove pfS pfI' pfI
 -- pfS'' :: Shift (u:Remove y g0') (u:Remove y g0')
    pfS'' = ShiftLater pfS'
-}

substUnshift :: In x s g
             -> LExp '[] s
             -> Shift i g g'
             -> LExp g' t
             -> LExp (Remove x g) t
substUnshift pfI s pfS e = undefined
{- Unshift pfS' $ subst pfI' s e
  where
    pfI' = inUnshift pfI pfS
    pfS' = inUnshiftRemove pfI pfS
-}
-- Evaluation --------------------------------------------

eval' :: EmptyCtx g -> LExp g s -> LVal s
eval' pfEmpty (Abs pfAdd e)       = absToLVal pfEmpty pfAdd e
eval' pfEmpty (App pfMerge e1 e2) = 
  case (eval' pfEmpty1 e1, eval pfEmpty2 e2) of
    (VAbs pfE pfA e1', e2') -> eval' EmptyNil e'
      where
        e' = transportDown (emptyRemove pfE pfA) $ subst (addIn pfA) e2' e1'
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
eval' pfEmpty (Put pf a) = VPut a
eval' pfEmpty (LetBang pfMerge e k) = 
  eval' EmptyNil $ transportDown pfEmpty2 (k a)
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
    a                   = fromVPut $ eval' pfEmpty1 e

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


eval :: EmptyCtx g -> LExp g s -> LExp '[] s
eval pfEmpty e = valToExp $ eval' pfEmpty e
