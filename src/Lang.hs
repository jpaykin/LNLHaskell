{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes
#-}

module Lang where

import Data.Kind
import Data.Constraint

import Types
import Context
  
data LExp :: Ctx -> LType -> * where
  Var :: forall x t g. SingletonCtx x t g -> LExp g t
  
  Abs :: forall x s t g g'. 
         AddCtx x s g g' 
      -> LExp g' t
      -> LExp g (s ⊸ t)
  App :: Merge g1 g2 g3
      -> LExp g1 (s ⊸ t)
      -> LExp g2 s
      -> LExp g3 t

  Unit :: LExp 'Empty One
  LetUnit :: Merge g1 g2 g3
          -> LExp g1 One
          -> LExp g2 t
          -> LExp g3 t

  Pair :: Merge g1 g2 g3
       -> LExp g1 t1
       -> LExp g2 t2
       -> LExp g3 (t1 ⊗ t2)
  LetPair :: Merge g1 g2 g3
       -> AddCtx x1 t1 g2 g2'
       -> AddCtx x2 t2 g2' g2''
       -> LExp g1 (t1 ⊗ t2)
       -> LExp g2'' r
       -> LExp g3   r

  Prod :: LExp g t1
       -> LExp g t2
       -> LExp g (t1 & t2)
  Fst  :: LExp g (t1 & t2)
       -> LExp g t1
  Snd  :: LExp g (t1 & t2)
       -> LExp g t2

  Inl  :: LExp g t1
       -> LExp g (t1 ⊕ t2)
  Inr  :: LExp g t2
       -> LExp g (t1 ⊕ t2)
  Case :: Merge g1 g2 g3
       -> AddCtx x1 s1 g2 g21
       -> AddCtx x2 s2 g2 g22
       -> LExp g1 (s1 ⊕ s2)
       -> LExp g21 t
       -> LExp g22 t
       -> LExp g3  t

  Put     :: a -> LExp 'Empty (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp g1 (Lower a)
      -> (a -> LExp g2 t)
      -> LExp g3 t

-- values

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



