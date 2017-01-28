{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts
#-}

module Lang where

import Prelude hiding (lookup)
import Data.Kind
import Data.Constraint
import Data.Proxy
import Data.Maybe

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

  evalDomain  :: ECtx lang g
              -> ExpDom dom lang g s
              -> SigEffect sig (LVal lang s)


data LExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Dom :: Language dom lang
      => Proxy dom 
      -> ExpDom dom lang g t 
      -> LExp lang g t

  Var :: SingletonCtx x t g -> LExp lang g t



-- Values -----------------------------------------------------

data LVal :: forall sig. Lang sig -> LType sig -> * where
  VDom  :: Language dom lang
        => Proxy dom -> ValDom dom lang s -> LVal lang s


-- Evaluation Context ------------------------------------

data ECtx (lang :: Lang sig) (g :: Ctx sig) where
  EEmpty :: ECtx lang 'Empty
  EN     :: ENCtx lang g -> ECtx lang ('N g)
data ENCtx (lang :: Lang sig) (g :: NCtx sig) where
  EEnd   :: Data lang s -> ENCtx lang ('End s)
  ECons  :: EUsage lang u -> ENCtx lang g -> ENCtx lang ('Cons u g)
data EUsage (lang :: Lang sig) (u :: Usage sig) where
  EUsed   :: Data lang s -> EUsage lang ('Used s)
  EUnused :: EUsage lang 'Unused

data Data (lang :: Lang sig) (s :: LType sig) where
  ExpData :: ECtx lang g -> LExp lang g s -> Data lang s
  ValData :: LVal lang s -> Data lang s

lookup :: In x s g -> ECtx lang g -> Data lang s
lookup (In pfI) (EN g) = lookupN pfI g

lookupN :: InN x s g -> ENCtx lang g -> Data lang s
lookupN InEnd           (EEnd v)            = v
lookupN (InHere _)      (ECons (EUsed v) _) = v
lookupN (InLater _ pfI) (ECons _ g)         = lookupN pfI g

eCtxMerge :: Merge g1 g2 g -> ECtx lang g -> (ECtx lang g1, ECtx lang g2)
eCtxMerge = undefined

addECtx :: AddCtx x s g g' -> ECtx lang g -> Data lang s -> ECtx lang g'
addECtx = undefined


-- Evaluation ---------------------------------------------

eval :: forall sig (lang :: Lang sig) (g :: Ctx sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp lang 'Empty s 
     -> SigEffect sig (LVal lang s)
eval e = eval' EEmpty e

eval' :: forall sig (lang :: Lang sig) (g :: Ctx sig) (s :: LType sig).
        Monad (SigEffect sig)
     => ECtx lang g
     -> LExp lang g s 
     -> SigEffect sig (LVal lang s)
eval' ρ (Var pfS)                      = 
  case lookup (singletonIn pfS) ρ of
    ExpData ρ e -> eval' ρ e
    ValData v   -> return v
eval' ρ (Dom (proxy :: Proxy dom) e)   = evalDomain @sig @dom ρ e

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

-- this function is partial if the value is not
-- in the specified domain
evalToValDom :: forall sig dom (lang :: Lang sig) g s.
                (CInLang dom lang, Monad (SigEffect sig))
             => Proxy dom -> ECtx lang g
             -> LExp lang g s -> SigEffect sig (ValDom dom lang s)
evalToValDom proxy ρ e = fromJust . fromLVal proxy <$> eval' ρ e
