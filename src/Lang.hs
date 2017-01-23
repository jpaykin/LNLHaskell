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

import Prelim
import Types
import Context
import Proofs
  
type Dom sig = (Lang sig -> Ctx sig -> LType sig -> *, Lang sig -> LType sig -> *)
newtype Lang sig = Lang [Dom sig]
type family ExpDom (dom :: Dom sig) :: Lang sig -> Ctx sig -> LType sig -> * where
  ExpDom '(exp,val) = exp
type family ValDom (dom :: Dom sig) :: Lang sig -> LType sig -> * where
  ValDom '(exp,val) = val

type family FromLang (lang :: Lang sig) :: [Dom sig] where
  FromLang ('Lang lang) = lang
class CInLang (x :: Dom sig) (lang :: Lang sig) where
  pfInLang :: InList x (FromLang lang)
instance CInList dom lang => CInLang dom ('Lang lang) where
  pfInLang = pfInList

class (CInLang dom lang, Monad (SigEffect sig))
   => Domain (dom :: Dom sig) (lang :: Lang sig)
instance (CInLang dom lang, Monad (SigEffect sig))
      => Domain (dom :: Dom sig) (lang :: Lang sig)

class Domain dom lang
   => Language (dom :: Dom sig) (lang :: Lang sig) where

  substDomain :: AddCtx x s g g' 
              -> LExp lang 'Empty s 
              -> ExpDom dom lang g' t 
              -> LExp lang g t

  evalDomain  :: ExpDom dom lang 'Empty s
              -> SigEffect sig (LVal lang s)

  valToExpDomain :: ValDom dom lang s 
                 -> ExpDom dom lang 'Empty s



data LExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Dom :: Language dom lang
      => Proxy dom 
      -> ExpDom dom lang g t 
      -> LExp lang g t

  Var :: SingletonCtx x t g -> LExp lang g t

  -- Abs :: AddCtx x s g g' 
  --     -> LExp lang g' t
  --     -> LExp lang g (s ⊸ t)

  -- App :: Merge g1 g2 g3
  --     -> LExp lang g1 (s ⊸ t)
  --     -> LExp lang g2 s
  --     -> LExp lang g3 t


-- Values -----------------------------------------------------

data LVal :: forall sig. Lang sig -> LType sig -> * where
  VDom  :: Language dom lang
        => Proxy dom -> ValDom dom lang s -> LVal lang s
  -- VAbs  :: AddCtx x s 'Empty g'
  --       -> LExp lang g' t
  --       -> LVal lang (s ⊸ t)

-- ValToExp -----------------------------------------------

valToExp :: forall sig (lang :: Lang sig) (t :: LType sig).
            LVal lang t -> LExp lang 'Empty t
valToExp (VDom (proxy :: Proxy dom) v) = Dom proxy $ valToExpDomain @_ @dom v
--valToExp (VAbs pfA e)   = Abs pfA e


-- Substitution --------------------------------------------

subst :: AddCtx x s g g' 
      -> LExp lang Empty s 
      -> LExp lang g' t 
      -> LExp lang g t
subst pfA s (Var pfS)      = 
  case singletonInInv (addIn pfA) pfS of {Dict -> 
  case addSingletonEmpty pfA pfS of {Dict -> 
    s
  }}
subst pfA s (Dom (proxy :: Proxy dom) e)  = substDomain @_ @dom pfA s e



-- Evaluation ---------------------------------------------

eval :: forall sig (lang :: Lang sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp lang 'Empty s 
     -> SigEffect sig (LExp lang 'Empty s)
eval e = fmap valToExp $ eval' e


eval' :: forall sig (lang :: Lang sig) (s :: LType sig).
         Monad (SigEffect sig)
      => LExp lang 'Empty s -> SigEffect sig (LVal lang s)
eval' (Dom (proxy :: Proxy dom) e)   = evalDomain @_ @dom e


-- Lift --------------------------------------------------------

data Lift (lang :: Lang sig) :: LType sig -> * where
  Suspend :: LExp lang 'Empty t -> Lift lang t

force :: Lift lang t -> LExp lang 'Empty t
force (Suspend e) = e

------------------------------------------------------

fromLVal :: forall sig dom (lang :: Lang sig) s.
            CInLang dom lang
         => Proxy dom -> LVal lang s -> Maybe (ValDom dom lang s)
fromLVal _ (VDom (proxy :: Proxy dom') v) = 
  case compareInList (pfInLang @_ @dom @lang) (pfInLang @_ @dom' @lang) of
    Nothing   -> Nothing
    Just Dict -> Just v

