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
import Proofs
  
type ExpDom sig = (Ctx sig -> LType sig -> *) -> Ctx sig -> LType sig -> *
type ValDom sig = (LType sig -> *) -> LType sig -> *
type Component sig = (ExpDom sig, ValDom sig)
type Dom sig = [Component sig]

type family Exp (component :: Component sig) :: ExpDom sig where
  Exp '(exp,_) = exp
type family Val (component :: Component sig) :: ValDom sig where
  Val '(_,val) = val

class    Monad (SigEffect sig) => WellScopedDom sig (dom :: Dom sig)
instance Monad (SigEffect sig) => WellScopedDom sig (dom :: Dom sig)

class    (WellScopedDom sig dom, CInList component dom) 
      => InDom sig component (dom :: Dom sig)
instance (WellScopedDom sig dom, CInList component dom) 
      => InDom sig component dom

class InDom sig component dom
   => Domain (component :: Component sig) (dom :: Dom sig) where

  substDomain :: Exp component ~ exp
              => Proxy component
              -> AddCtx x s g g' 
              -> LExp dom 'Empty s 
              -> exp (LExp dom) g' t 
              -> LExp dom g t

  evalDomain  :: Exp component ~ exp
              => Proxy component
              -> exp (LExp dom) 'Empty s
              -> SigEffect sig (LVal dom s)

  valToExpDomain :: (Exp component ~ exp, Val component ~ val)
                 => Proxy component 
                 -> val (LVal dom) s 
                 -> exp (LExp dom) 'Empty s



data LExp :: forall sig. Dom sig -> Ctx sig -> LType sig -> * where
  Dom :: Domain '(exp,val) dom
      => Proxy '(exp,val)
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


-- Values -----------------------------------------------------

data LVal :: forall sig. Dom sig -> LType sig -> * where
  VDom  :: Domain '(exp,val) dom
        => Proxy '(exp,val)
        -> val (LVal dom) s -> LVal dom s
  VAbs  :: AddCtx x s 'Empty g'
        -> LExp dom g' t
        -> LVal dom (s ⊸ t)

-- ValToExp -----------------------------------------------

valToExp :: forall sig (dom :: Dom sig) (t :: LType sig).
            LVal dom t -> LExp dom 'Empty t
valToExp (VDom proxy v) = Dom proxy $ valToExpDomain proxy v
valToExp (VAbs pfA e)   = Abs pfA e

-- Substitution --------------------------------------------

subst :: AddCtx x s g g' 
      -> LExp dom Empty s 
      -> LExp dom g' t 
      -> LExp dom g t
subst pfA s (Dom proxy e) = substDomain proxy pfA s e
subst pfA s (Abs pfA' e)   = undefined
subst pfA s (App pfM e1 e2)= 
  case mergeAddSplit pfM pfA of
    Left  (pfA1,pfM1) -> App pfM1 (subst pfA1 s e1) e2
    Right (pfA2,pfM2) -> App pfM2 e1 (subst pfA2 s e2)


-- Evaluation ---------------------------------------------

eval :: forall sig (dom :: Dom sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp dom 'Empty s 
     -> SigEffect sig (LExp dom 'Empty s)
eval e = fmap valToExp $ eval' e


eval' :: forall sig (dom :: Dom sig) (s :: LType sig).
         Monad (SigEffect sig)
      => LExp dom 'Empty s -> SigEffect sig (LVal dom s)
eval' (Dom proxy e)         = evalDomain proxy e
eval' (Abs pfA e)       = return $ VAbs pfA e
eval' (App pfM e1 e2) = 
  case mergeEmpty pfM of {Dict -> do
    VAbs pfA e1' <- eval' e1
    e2'          <- eval e2
    case addRemoveEquiv pfA of {Dict -> 
    eval' $ subst pfA e2' e1'
  }}


-- Lift --------------------------------------------------------

data Lift (dom :: Dom sig) :: LType sig -> * where
  Suspend :: LExp dom 'Empty t -> Lift dom t

force :: Lift dom t -> LExp dom 'Empty t
force (Suspend e) = e

------------------------------------------------------


proxyToInList :: forall sig (dom :: Dom sig) component.
                 CInList component dom 
              => Proxy component
              -> InList component dom
proxyToInList _ = pfInList @_ @component


fromLVal :: forall sig (dom :: Dom sig) exp val s.
            CInList '(exp,val) dom
         => Proxy '(exp,val)
         -> LVal dom s -> Maybe (val (LVal dom) s)
fromLVal proxy (VDom proxy' v) =
  case compareInList (proxyToInList @sig @dom proxy) (proxyToInList @sig @dom proxy') of
    Nothing   -> Nothing
    Just Dict -> Just v

