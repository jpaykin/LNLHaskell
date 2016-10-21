{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase
#-}

module Lang where

import Data.Kind
import Data.Constraint

import Types
import Frame


  
data LExp :: Frame -> Ctx -> LType -> * where
  Var :: forall x t f1 f2 g. SingletonCtx x t f1 f2 g -> LExp (Splice f1 x f2) g t
  Abs :: forall x s f1 f2 t g g'. 
         AddCtx x s f1 f2 g g' 
      -> LExp (Splice f1 x f2) g' t
      -> LExp (Splice f1 x f2) g (s ⊸ t)
  App :: Merge g1 g2 g3
      -> LExp f g1 (s ⊸ t)
      -> LExp f g2 s
      -> LExp f g3 t

  Put     :: forall (f::Frame) (g::Ctx) a. EmptyCtx f g -> a -> LExp f g (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp f g1 (Lower a)
      -> (a -> LExp f g2 t)
      -> LExp f g3 t

-- values

data LVal :: Frame -> Ctx -> LType -> * where
  VAbs :: forall x s f f1 f2 t g g'. 
         EmptyCtx (Splice f1 x f2) g
      -> AddCtx x s f1 f2 g g' 
      -> LExp (Splice f1 x f2) g' t
      -> LVal (Splice f1 x f2) g (s ⊸ t)
  VPut :: EmptyCtx f g -> a -> LVal f g (Lower a)

valToExp :: LVal f g t -> LExp f g t
valToExp (VAbs _ pfAdd e) = Abs pfAdd e
valToExp (VPut pfEmpty a) = Put pfEmpty a


subst :: forall x s f f1 f2 t g0 g1 g2 g3.
         (Splice f1 x f2 ~ f) 
      => EmptyCtx f g1
      -> AddCtx x s f1 f2 g0 g2 
      -> LExp f g1 s 
      -> LExp f g2 t 
      -> LExp f g0 t
subst pfEmpty1 pfAdd s (Var pfSing) = 
  case addSingletonInv pfAdd pfSing of {Dict -> 
  let pfEmpty2 = addSingletonEmpty pfAdd pfSing
  in case emptyUnique pfEmpty1 pfEmpty2 of Dict -> s
  } 
subst pfEmpty pfAdd s (Abs pfAdd2 e')      = substAbs pfEmpty s pfAdd pfAdd2 e'
subst pfEmpty pfAdd s (App pfMerge e1 e2)  = substApp pfEmpty s pfAdd pfMerge e1 e2
subst _       pfAdd s (Put _ a)            = case pfAdd of 
subst _       pfAdd s (LetBang _ _ _)      = case pfAdd of
  

substAbs :: (Splice f1 x f2 ~ f)
         => EmptyCtx f g
         -> LExp f g s
         -> AddCtx x s  f1  f2  g0  g1
         -> AddCtx y t1 f1' f2' g1 g2
         -> LExp (Splice f1' y f2') g2 t2
         -> LExp f g0 (t1 ⊸ t2)
substAbs = undefined

substApp :: (Splice f1 x f2 ~ f)
         => EmptyCtx f g
         -> LExp f g s
         -> AddCtx x s f1 f2 g0 g3 
         -> Merge g1 g2 g3
         -> LExp f g1 (t1 ⊸ t2)
         -> LExp f g2 t1
         -> LExp f g0 t2
substApp = undefined


fromVPut :: forall f g a. LVal f g (Lower a) -> a
fromVPut (VPut _ a) = a

eval' :: forall f g s. EmptyCtx f g -> LExp f g s -> LVal f g s
-- Abstraction is a value
eval' pfEmpty (Abs pfAdd e)           = VAbs pfEmpty pfAdd e
-- Application
eval' pfEmpty (App pfMerge e1 e2)     = 
  case (eval' pfEmpty1 e1, eval pfEmpty2 e2) of
    (VAbs _ pfAdd e1', e2') -> 
       case emptyUnique pfEmpty1 pfEmpty of
         Dict -> eval' pfEmpty $ subst pfEmpty2 pfAdd e2' e1'
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
-- Put is a value
eval' pfEmpty (Put _ a)               = VPut pfEmpty a
-- LetBang
eval' pfEmpty (LetBang pfMerge e k) = 
  case emptyUnique pfEmpty2 pfEmpty of Dict -> eval' pfEmpty2 $ k a
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
    v                   = eval' pfEmpty1 e
    a                   = fromVPut v


eval :: forall f g s. EmptyCtx f g -> LExp f g s -> LExp f g s
eval pfEmpty e = valToExp $ eval' pfEmpty e

