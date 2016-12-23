{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts
#-}

module Lang where

import Data.Kind
import Data.Constraint
import Data.Proxy

import Types
import Context
  
type ExpDom sig = (Ctx sig -> LType sig -> *) -> Ctx sig -> LType sig -> *
type ValDom sig = (LType sig -> *) -> LType sig -> *
type Dom sig = [(ExpDom sig, ValDom sig)]

class    Monad (SigEffect sig) => WellScopedDom sig (dom :: Dom sig)
instance Monad (SigEffect sig) => WellScopedDom sig (dom :: Dom sig)

class    (WellScopedDom sig dom, CInList '(exp,val) dom) 
      => InDom sig exp val (dom :: Dom sig)
instance (WellScopedDom sig dom, CInList '(exp,val) dom) 
      => InDom sig exp val dom

class InDom sig exp val dom
   => Domain (exp :: ExpDom sig) (val :: ValDom sig) (dom :: Dom sig) where

  substDomain :: (Proxy exp,Proxy val)
              -> AddCtx x s g g' 
              -> LExp dom 'Empty s 
              -> exp (LExp dom) g' t 
              -> LExp dom g t

  evalDomain  :: (Proxy exp,Proxy val)
              -> exp (LExp dom) 'Empty s
              -> SigEffect sig (LVal dom s)

  valToExpDomain :: (Proxy exp, Proxy val)
                 -> val (LVal dom) s 
                 -> exp (LExp dom) 'Empty s



data LExp :: forall sig. Dom sig -> Ctx sig -> LType sig -> * where
  Dom :: Domain exp val dom
      => (Proxy exp,Proxy val)
      -> exp (LExp dom) g t 
      -> LExp dom g t

  Var :: SingletonCtx x t g -> LExp dom g t

  Abs :: AddCtx x s g g' 
      -> LExp dom g' t
      -> LExp dom g (s ⊸ t)
  App :: Merge g1 g2 g3
      -> LExp dom g1 (s ⊸ t)
      -> LExp dom g2 s
      -> LExp dom g3 t

{-  

  Unit :: LExp dom 'Empty One
  LetUnit :: Merge g1 g2 g3
          -> LExp dom g1 One
          -> LExp dom g2 t
          -> LExp dom g3 t

  Pair :: Merge g1 g2 g3
       -> LExp dom g1 t1
       -> LExp dom g2 t2
       -> LExp dom g3 (t1 ⊗ t2)
  LetPair :: Merge g1 g2 g3
       -> AddCtx x1 t1 g2 g2'
       -> AddCtx x2 t2 g2' g2''
       -> LExp dom g1 (t1 ⊗ t2)
       -> LExp dom g2'' r
       -> LExp dom g3   r

  Prod :: LExp dom g t1
       -> LExp dom g t2
       -> LExp dom g (t1 & t2)
  Fst  :: LExp dom g (t1 & t2)
       -> LExp dom g t1
  Snd  :: LExp dom g (t1 & t2)
       -> LExp dom g t2

  Inl  :: LExp dom g t1
       -> LExp dom g (t1 ⊕ t2)
  Inr  :: LExp dom g t2
       -> LExp dom g (t1 ⊕ t2)
  Case :: Merge g1 g2 g3
       -> AddCtx x1 s1 g2 g21
       -> AddCtx x2 s2 g2 g22
       -> LExp dom g1 (s1 ⊕ s2)
       -> LExp dom g21 t
       -> LExp dom g22 t
       -> LExp dom g3  t

  Put     :: a -> LExp dom 'Empty (Lower a)
  LetBang :: Merge g1 g2 g
      -> LExp dom g1 (Lower a)
      -> (a -> LExp dom g2 t)
      -> LExp dom g t
-}

-- Values -----------------------------------------------------

data LVal :: forall sig. Dom sig -> LType sig -> * where
  VDom  :: Domain exp val dom
        => (Proxy exp,Proxy val) 
        -> val (LVal dom) s -> LVal dom s
  VAbs  :: AddCtx x s 'Empty g'
        -> LExp dom g' t
        -> LVal dom (s ⊸ t)

{-  VUnit :: LVal dom One
  VPut  :: a -> LVal dom (Lower a)
  VPair :: LVal dom t1 -> LVal dom t2 -> LVal dom (t1 ⊗ t2)
  VProd :: LVal dom t1 -> LVal dom t2 -> LVal dom (t1 & t2)
  VInl  :: LVal dom t1 -> LVal dom (t1 ⊕ t2)
  VInr  :: LVal dom t2 -> LVal dom (t1 ⊕ t2)
-}

valToExp :: forall sig (dom :: Dom sig) (t :: LType sig).
            LVal dom t -> LExp dom 'Empty t
valToExp (VDom proxy v) = Dom proxy $ valToExpDomain proxy v
-- valToExp VUnit           = Unit
-- valToExp (VAbs pfAdd e)  = Abs pfAdd e
-- valToExp (VPut a)        = Put a
-- valToExp (VPair v1 v2)   = Pair MergeE (valToExp v1) (valToExp v2)
-- valToExp (VProd v1 v2)   = Prod (valToExp v1) (valToExp v2)
-- valToExp (VInl v)        = Inl $ valToExp v
-- valToExp (VInr v)        = Inr $ valToExp v




-- Lift --------------------------------------------------------

data Lift (dom :: Dom sig) :: LType sig -> * where
  Suspend :: LExp dom 'Empty t -> Lift dom t

force :: Lift dom t -> LExp dom 'Empty t
force (Suspend e) = e


------------------------------------------------------


proxyToInList :: forall sig (dom :: Dom sig) exp val.
                 CInList '(exp,val) dom 
              => (Proxy exp, Proxy val)
              -> InList '(exp,val) dom
proxyToInList _ = pfInList @_ @'(exp,val)


fromLVal :: forall sig (dom :: Dom sig) exp val s.
            CInList '(exp,val) dom
         => (Proxy exp,Proxy val)
         -> LVal dom s -> Maybe (val (LVal dom) s)
fromLVal proxy (VDom proxy' v) =
  case compareInList (proxyToInList @sig @dom proxy) (proxyToInList @sig @dom proxy') of
    Nothing   -> Nothing
    Just Dict -> Just v

