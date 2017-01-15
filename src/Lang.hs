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
type Dom sig = (ExpDom sig, ValDom sig)
type Lang sig = [Dom sig]


class (CInList dom lang, Monad (SigEffect sig))
   => Domain (dom :: Dom sig) (lang :: Lang sig)
instance (CInList dom lang, Monad (SigEffect sig))
      => Domain (dom :: Dom sig) (lang :: Lang sig)

class Domain dom lang
   => Language (dom :: Dom sig) (lang :: Lang sig) where

  substDomain :: dom ~ '(exp,val)
              => Proxy '(exp,val)
              -> AddCtx x s g g' 
              -> LExp lang 'Empty s 
              -> exp (LExp lang) g' t 
              -> LExp lang g t

  evalDomain  :: dom ~ '(exp,val)
              => Proxy '(exp,val)
              -> exp (LExp lang) 'Empty s
              -> SigEffect sig (LVal lang s)

  valToExpDomain :: dom ~ '(exp,val)
                 => Proxy '(exp,val)
                 -> val (LVal lang) s 
                 -> exp (LExp lang) 'Empty s



data LExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Dom :: Language '(exp,val) lang
      => Proxy '(exp,val)
      -> exp (LExp lang) g t 
      -> LExp lang g t

  Var :: SingletonCtx x t g -> LExp lang g t

  Abs :: AddCtx x s g g' 
      -> LExp lang g' t
      -> LExp lang g (s ⊸ t)

  App :: Merge g1 g2 g3
      -> LExp lang g1 (s ⊸ t)
      -> LExp lang g2 s
      -> LExp lang g3 t


-- Values -----------------------------------------------------

data LVal :: forall sig. Lang sig -> LType sig -> * where
  VDom  :: Language '(exp,val) lang
        => Proxy '(exp,val)
        -> val (LVal lang) s -> LVal lang s
  VAbs  :: AddCtx x s 'Empty g'
        -> LExp lang g' t
        -> LVal lang (s ⊸ t)

-- ValToExp -----------------------------------------------

valToExp :: forall sig (lang :: Lang sig) (t :: LType sig).
            LVal lang t -> LExp lang 'Empty t
valToExp (VDom proxy v) = Dom proxy $ valToExpDomain proxy v
valToExp (VAbs pfA e)   = Abs pfA e

-- Substitution --------------------------------------------

subst :: AddCtx x s g g' 
      -> LExp lang Empty s 
      -> LExp lang g' t 
      -> LExp lang g t
subst pfA s (Dom proxy e) = substDomain proxy pfA s e
subst pfA s (Abs pfA' e)   = undefined
subst pfA s (App pfM e1 e2)= 
  case mergeAddSplit pfM pfA of
    Left  (pfA1,pfM1) -> App pfM1 (subst pfA1 s e1) e2
    Right (pfA2,pfM2) -> App pfM2 e1 (subst pfA2 s e2)


-- Evaluation ---------------------------------------------

eval :: forall sig (lang :: Lang sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp lang 'Empty s 
     -> SigEffect sig (LExp lang 'Empty s)
eval e = fmap valToExp $ eval' e


eval' :: forall sig (lang :: Lang sig) (s :: LType sig).
         Monad (SigEffect sig)
      => LExp lang 'Empty s -> SigEffect sig (LVal lang s)
eval' (Dom proxy e)   = evalDomain proxy e
eval' (Abs pfA e)     = return $ VAbs pfA e
eval' (App pfM e1 e2) = 
  case mergeEmpty pfM of {Dict -> do
    VAbs pfA e1' <- eval' e1
    e2'          <- eval e2
    case addRemoveEquiv pfA of {Dict -> 
    eval' $ subst pfA e2' e1'
  }}


-- Lift --------------------------------------------------------

data Lift (lang :: Lang sig) :: LType sig -> * where
  Suspend :: LExp lang 'Empty t -> Lift lang t

force :: Lift lang t -> LExp lang 'Empty t
force (Suspend e) = e

------------------------------------------------------


proxyToInList :: forall sig (lang :: Lang sig) dom.
                 CInList dom lang
              => Proxy dom
              -> InList dom lang
proxyToInList _ = pfInList @_ @dom


fromLVal :: forall sig (lang :: Lang sig) exp val s.
            CInList '(exp,val) lang
         => Proxy '(exp,val)
         -> LVal lang s -> Maybe (val (LVal lang) s)
fromLVal proxy (VDom proxy' v) =
  case compareInList (proxyToInList @sig @lang proxy) 
                     (proxyToInList @sig @lang proxy') of
    Nothing   -> Nothing
    Just Dict -> Just v

