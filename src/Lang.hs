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

-- Lift --------------------------------------------------------

data Lift :: LType -> * where
  Suspend :: forall t. LExp 'Empty t -> Lift t

-- force should also evaluate the expression
force :: forall t. Lift t -> LExp 'Empty t
force (Suspend e) = e

