{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase
#-}

module Interface where

import Data.Kind
import Data.Constraint

import Types
import Context
import Proofs
import Classes
import Lang
import Subst

var :: forall x g t. 
       SIdent x -> LExp (FSingletonCtx x t) t
var x = Var $ fSingletonCtx x


λ :: forall s t g g'. (KnownCtx g, CAddCtx (Fresh g) s g g')
  => (LExp (FSingletonCtx (Fresh g) s) s 
      -> LExp g' t)
  -> LExp g (s ⊸ t)
λ f = Abs pfA (f varx) where
  pfA  = addCtx @(Fresh g) @s @g @g'
  varx = var $ addToSIdent pfA

app :: CMerge g1 g2 g3 
    => LExp g1 (s ⊸ t)
    -> LExp g2 s
    -> LExp g3 t
e1 `app` e2 = App merge e1 e2

put :: a -> LExp '[] (Lower a)
put a = Put EmptyNil a

(>!) :: CMerge g1 g2 g3
     => LExp g1 (Lower a)
     -> (a -> LExp g2 t)
     -> LExp g3 t
(>!) = LetBang merge


data Lift :: LType -> * where
  Suspend :: forall t. LExp '[] t -> Lift t


data Lin a where
  Lin :: Lift (Lower a) -> Lin a


coerce :: CEmptyCtx g => LExp g t -> LExp '[] t
coerce e = transportDown emptyCtx e


-- We've got some problems here.

instance Functor Lin where
  -- f :: a -> b
  -- a :: Lin a ~ Lift f (Lower a)
  -- fmap f a :: Lift (Lower b)
  fmap f (Lin (Suspend e)) = Lin . Suspend $ e >! \ x → put (f x)
instance Applicative Lin where
  pure a = Lin $ suspend (put a)
  -- a :: Lift (Lower a) 
  -- f :: Lift (Lower (a -> b))
  -- f <*> a :: Lift (Lower b)
  Lin (Suspend f) <*> Lin (Suspend e) = Lin . Suspend $ e >! \ x -> 
                                                        f >! \ f' -> 
                                                        put (f' x)
instance Monad Lin where
  -- e :: Lin a = Lift (Lower a)
  -- f :: a -> Lift (Lower b)
  Lin (Suspend e) >>= f  = Lin . Suspend $ e >! \ x -> forceL (f x)

-- force should also evaluate the expression
force :: forall t. Lift t -> LExp '[] t
-- e :: LExp g t
force (Suspend e) = coerce $ eval emptyCtx e


forceL :: Lin a -> LExp '[] (Lower a)
forceL (Lin e) = force e

suspend :: LExp '[] a -> Lift a
suspend = Suspend 

suspendL :: LExp '[] (Lower a) -> Lin a
suspendL = Lin . Suspend 

evalC :: CEmptyCtx g => LExp g a -> LExp '[] a
evalC e = eval emptyCtx e

evalL :: Lin a -> Lin a
evalL (Lin e) = Lin $ evalL' e where
  evalL' :: forall a. Lift (Lower a) -> Lift (Lower a)
  evalL' (Suspend e) = Suspend $ eval (emptyCtx) e

evalVal :: Lin a -> LVal (Lower a) 
evalVal (Lin (Suspend e)) = eval' EmptyNil e

run :: Lin a -> a
run e = case evalVal e of VPut a -> a
