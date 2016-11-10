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
      -> LExp 'Empty s
      -> LExp g t
      -> LExp (Remove x g) t
subst pfI s (Var pfS)                       = substVar     pfI s pfS
subst pfI s (Abs pfA e')                    = substAbs     pfI s pfA e'
subst pfI s (App pfM e1 e2)                 = substApp     pfI s pfM e1 e2
subst pfI s (LetUnit pfM e1 e2)             = substLetUnit pfI s pfM e1 e2
subst pfI s (Pair pfM e1 e2)                = substPair    pfI s pfM e1 e2
subst pfI s (LetPair pfM pfA pfA' e1 e2)    = substLetPair pfI s pfM pfA pfA' e1 e2
subst pfI s (Prod e1 e2)                    = Prod (subst pfI s e1) (subst pfI s e2)
subst pfI s (Fst e)                         = Fst $ subst pfI s e
subst pfI s (Snd e)                         = Snd $ subst pfI s e
subst pfI s (Inl e)                         = Inl $ subst pfI s e
subst pfI s (Inr e)                         = Inr $ subst pfI s e
subst pfI s (Case pfM pfA1 pfA2 e1 e21 e22) = substCase pfI s pfM pfA1 pfA2 e1 e21 e22
subst pfI s (Put a)                         = case pfI of 
subst pfI s (LetBang pfM e f)               = substLetBang pfI s pfM e f


substVal :: In x s g -> LVal s -> LExp g t -> LExp (Remove x g) t
substVal pfI v e = subst pfI (valToExp v) e

substVar :: In x s g
         -> LExp 'Empty s
         -> SingletonCtx y t g
         -> LExp (Remove x g) t
substVar pfI s pfS = case singletonInInv pfI pfS of {Dict -> 
                     case singletonRemove pfS of Dict -> s}

substAbs :: In x s g
         -> LExp 'Empty s
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
    pfA' = inAddRemoveLater pfI pfA


substApp  :: In x s g 
          -> LExp 'Empty s
          -> Merge g1 g2 g
          -> LExp g1 (t1 ⊸ t2)
          -> LExp g2 t1
          -> LExp (Remove x g) t2
substApp pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> App (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> App (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substLetUnit :: In x s g
             -> LExp 'Empty s
             -> Merge g1 g2 g
             -> LExp g1 One
             -> LExp g2 t
             -> LExp (Remove x g) t
substLetUnit pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetUnit (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> LetUnit (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substPair :: In x s g
          -> LExp 'Empty s
          -> Merge g1 g2 g
          -> LExp g1 t1
          -> LExp g2 t2
          -> LExp (Remove x g) (t1 ⊗ t2)
substPair pfI s pfM e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> Pair (mergeIn1 pfM pfI1) (subst pfI1 s e1) e2
    Right pfI2 -> Pair (mergeIn2 pfM pfI2) e1 (subst pfI2 s e2)

substLetPair :: forall x s t g1 g2 g x1 x2 s1 s2 g2' g2''.
                In x s g
             -> LExp 'Empty s
             -> Merge g1 g2 g
             -> AddCtx x1 s1 g2 g2'
             -> AddCtx x2 s2 g2' g2''
             -> LExp g1 (s1 ⊗ s2)
             -> LExp g2'' t
             -> LExp (Remove x g) t
substLetPair pfI s pfM pfA1 pfA2 e e' =
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetPair (mergeIn1 pfM pfI1) pfA1 pfA2 (subst pfI1 s e) e'
    Right pfI2 -> LetPair pfM' pfA1' pfA2' e e''
      where
     -- pfI2 :: In x s g2
        pfI2' :: In x s g2'
        pfI2' = inAdd pfI2 pfA1
        pfI2'' :: In x s g2''
        pfI2'' = inAdd pfI2' pfA2
        pfM' :: Merge g1 (Remove x g2) (Remove x g)
        pfM' = mergeIn2 pfM pfI2
        pfA1' :: AddCtx x1 s1 (Remove x g2) (Remove x g2')
        pfA1' = inAddRemoveLater pfI2 pfA1
        pfA2' :: AddCtx x2 s2 (Remove x g2') (Remove x g2'')
        pfA2' = inAddRemoveLater pfI2' pfA2
        e'' :: LExp (Remove x g2'') t
        e'' = subst pfI2'' s e'


substCase :: forall x s g g1 g2 x1 s1 g21 x2 s2 g22 t.
             In x s g
          -> LExp 'Empty s
          -> Merge g1 g2 g
          -> AddCtx x1 s1 g2 g21
          -> AddCtx x2 s2 g2 g22
          -> LExp g1 (s1 ⊕ s2)
          -> LExp g21 t
          -> LExp g22 t
          -> LExp (Remove x g) t
substCase pfI s pfM pfA1 pfA2 e e1 e2 = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> Case (mergeIn1 pfM pfI1) pfA1 pfA2 (subst pfI1 s e) e1 e2
    Right pfI2 -> Case pfM' pfA1' pfA2' e e1' e2'
      where
        pfM' :: Merge g1 (Remove x g2) (Remove x g)
        pfM' = mergeIn2 pfM pfI2
        pfA1' :: AddCtx x1 s1 (Remove x g2) (Remove x g21)
        pfA1' = inAddRemoveLater pfI2 pfA1
        pfA2' :: AddCtx x2 s2 (Remove x g2) (Remove x g22)
        pfA2' = inAddRemoveLater pfI2 pfA2
        pfI21 :: In x s g21
        pfI21 = inAdd pfI2 pfA1
        pfI22 :: In x s g22
        pfI22 = inAdd pfI2 pfA2
        e1' :: LExp (Remove x g21) t
        e1' = subst pfI21 s e1
        e2' :: LExp (Remove x g22) t
        e2' = subst pfI22 s e2


substLetBang :: In x s g
             -> LExp 'Empty s
             -> Merge g1 g2 g
             -> LExp g1 (Lower a)
             -> (a -> LExp g2 t)
             -> LExp (Remove x g) t
substLetBang pfI s pfM e f = 
  case mergeInSplit pfM pfI of
    Left  pfI1 -> LetBang (mergeIn1 pfM pfI1) (subst pfI1 s e) f
    Right pfI2 -> LetBang (mergeIn2 pfM pfI2) e (\x -> subst pfI2 s (f x))

-- Evaluation --------------------------------------------

eval' :: LExp 'Empty s -> LVal s
eval' (Abs pfA e)       = VAbs pfA e
eval' (App pfM e1 e2) = 
  case mergeEmpty pfM of {Dict ->
  case (eval' e1, eval e2) of
    (VAbs pfA e1', e2') -> 
      case addRemoveEquiv pfA of Dict -> eval' $ subst (addIn pfA) e2' e1'
  }
eval' Unit                          = VUnit
eval' (LetUnit pfM e1 e2)           = evalLetUnit pfM e1 e2
eval' (Pair pfM e1 e2)              = 
  case mergeEmpty pfM of Dict -> VPair (eval' e1) (eval' e2)
eval' (LetPair pfM pfA1 pfA2 e1 e2) = evalLetPair pfM pfA1 pfA2 e1 e2
eval' (Prod e1 e2)                  = VProd (eval' e1) (eval' e2)
eval' (Fst e)                       = 
  case eval' e of VProd v1 v2 -> v1
eval' (Snd e)                       =
  case eval' e of VProd v1 v2 -> v2
eval' (Inl e)                       = VInl $ eval' e
eval' (Inr e)                       = VInr $ eval' e
eval' (Case pfM pfA1 pfA2 e e1 e2)  = evalCase pfM pfA1 pfA2 e e1 e2
eval' (Put a)                       = VPut a
eval' (LetBang pfM e f)             = evalLetBang pfM e f

evalLetUnit :: Merge g1 g2 'Empty
            -> LExp g1 One
            -> LExp g2 t
            -> LVal t
evalLetUnit pfM e1 e2 =
  case mergeEmpty pfM of {Dict ->
  case eval' e1 of VUnit -> eval' e2
  }

evalLetPair :: forall g1 g2 x1 x2 t1 t2 g2' g2'' r. 
            Merge g1 g2 'Empty
         -> AddCtx x1 t1 g2 g2'
         -> AddCtx x2 t2 g2' g2''
         -> LExp g1 (t1 ⊗ t2)
         -> LExp g2'' r
         -> LVal r
evalLetPair pfM pfA1 pfA2 e1 e2 = 
  case mergeEmpty pfM of {Dict ->
  case eval' e1 of 
    VPair v1 v2 -> 
      case addRemoveEquiv pfA1 of {Dict ->
      case addRemoveEquiv pfA2 of {Dict -> eval' e2''}}
      where
        e2' :: LExp (Remove x2 g2'') r
        e2' = substVal pfI2 v2 e2
        e2'' :: LExp (Remove x1 (Remove x2 g2'')) r
        e2'' = substVal pfI1'' v1 e2'
  }
  where
    pfD :: Disjoint x1 x2
    pfD = disjointIn pfI1 pfA2
    pfI1 :: In x1 t1 g2'
    pfI1 = addIn pfA1
    pfI1' :: In x1 t1 g2''
    pfI1' = inAdd pfI1 pfA2
    pfI1'' :: In x1 t1 (Remove x2 g2'')
    pfI1'' = disjointRemove pfD pfI1' pfI2
    pfI2 :: In x2 t2 g2''
    pfI2 = addIn pfA2

evalCase :: forall g g1 g2 x1 s1 g21 x2 s2 g22 t.
            Merge g1 g2 'Empty
         -> AddCtx x1 s1 g2 g21
         -> AddCtx x2 s2 g2 g22
         -> LExp g1 (s1 ⊕ s2)
         -> LExp g21 t
         -> LExp g22 t
         -> LVal t
evalCase pfM pfA1 pfA2 e e1 e2 = 
  case mergeEmpty pfM      of {Dict -> 
  case addRemoveEquiv pfA1 of {Dict ->
  case addRemoveEquiv pfA2 of {Dict -> 
  case eval' e of
    VInl v1 -> eval' (substVal pfI1 v1 e1)
    VInr v2 -> eval' (substVal pfI2 v2 e2)
  }}}
  where
    pfI1 :: In x1 s1 g21
    pfI1 = addIn pfA1
    pfI2 = addIn pfA2
    

evalLetBang :: forall g1 g2 a t.
               Merge g1 g2 'Empty
            -> LExp g1 (Lower a)
            -> (a -> LExp g2 t)
            -> LVal t
evalLetBang pfM e f = 
  case mergeEmpty pfM of {Dict -> -- g1,g2 = Empty
  case eval' e        of {VPut a -> 
    eval' $ f a
  }}
    

eval :: LExp 'Empty s -> LExp 'Empty s
eval e = valToExp $ eval' e
