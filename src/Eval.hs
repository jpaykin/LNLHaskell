{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, LambdaCase,
             EmptyCase
#-}

module Eval where

import Data.Kind
import Data.Constraint

import Types
import Context
import Proofs
import Lang 
import Subst

-- Evaluation --------------------------------------------

eval' :: LExp 'Empty s -> LVal s
eval' (Abs pfA e)       = VAbs pfA e
eval' (App pfM e1 e2) = 
  case mergeEmpty pfM of {Dict ->
  case (eval' e1, eval e2) of
    (VAbs pfA e1', e2') -> 
      case addRemoveEquiv pfA of Dict -> eval' $ subst pfA e2' e1'
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

substVal :: In x s g -> LVal s -> LExp g t -> LExp (Remove x g) t
substVal pfI v e = subst' pfI (valToExp v) e


-- Values -----------------------------------------------------

data LVal :: LType -> * where
  VUnit :: LVal One
  VAbs :: forall x s t g'.
         AddCtx x s 'Empty g'
      -> LExp g' t
      -> LVal (s ⊸ t)
  VPut :: a -> LVal (Lower a)
  VPair :: LVal t1 -> LVal t2 -> LVal (t1 ⊗ t2)
  VProd :: LVal t1 -> LVal t2 -> LVal (t1 & t2)
  VInl  :: LVal t1 -> LVal (t1 ⊕ t2)
  VInr  :: LVal t2 -> LVal (t1 ⊕ t2)

valToExp :: LVal t -> LExp 'Empty t
valToExp VUnit           = Unit
valToExp (VAbs pfAdd e)  = Abs pfAdd e
valToExp (VPut a)        = Put a
valToExp (VPair v1 v2)   = Pair MergeE (valToExp v1) (valToExp v2)
valToExp (VProd v1 v2)   = Prod (valToExp v1) (valToExp v2)
valToExp (VInl v)        = Inl $ valToExp v
valToExp (VInr v)        = Inr $ valToExp v
