{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase
#-}

module Interface where

import Data.Kind
import Data.Constraint

import Types
import Context
import Classes
import Lang

var :: forall x g t. CSingletonCtx x t g 
    => LExp g t
var = Var (singletonCtx @x @t)

λ :: forall x s t g g'. CAddCtx x s g g' 
  => LExp g' t 
  -> LExp g (s ⊸ t)
λ t = Abs (addCtx @x @_) t

(@@) :: CMerge g1 g2 g3 
    => LExp g1 (s ⊸ t)
    -> LExp g2 s
    -> LExp g3 t
e1 @@ e2 = App merge e1 e2

app :: LExp '[] (s ⊸ t)
      -> LExp g s
      -> LExp g t
e1 `app` e2 = App MergeEL e1 e2

put :: a -> LExp '[] (Lower a)
put a = Put EmptyNil a

(>!) :: CMerge g1 g2 g3
     => LExp g1 (Lower a)
     -> (a -> LExp g2 t)
     -> LExp g3 t
(>!) = LetBang merge


data Lift :: LType -> * where
  Suspend :: forall g t. CEmptyCtx g => LExp g t -> Lift t


data Lin a where
  Lin :: Lift (Lower a) -> Lin a


-- fmapLExp :: forall f g a b. EmptyCtx f g -> (a -> b) -> 
--                             LExp g (Lower a) -> LExp g (Lower b)
-- fmapLExp pfEmpty g e = LetBang (mergeEmpty3 pfEmpty) e $ \x -> Put pfEmpty (g x)

-- fmapLift :: forall f a b. (a -> b) -> Lift f (Lower a) -> Lift f (Lower b)
-- fmapLift g (Suspend e) = Suspend $ fmapLExp (emptyCtx @f) g e

-- appLExp :: forall f g g' a b. EmptyCtx f g 
--         -> LExp g (Lower (a -> b))
--         -> LExp g (Lower a)
--         -> LExp g (Lower b)
-- appLExp pfEmpty e1 e2 = LetBang (mergeEmpty3 pfEmpty) e1 (\g -> fmapLExp pfEmpty g e2)

-- appLift :: forall f a b. Lift f (Lower (a -> b)) -> Lift f (Lower a) -> Lift f (Lower b)
-- appLift (Suspend e1) (Suspend e2) = Suspend $ appLExp (emptyCtx @f) e1 (coerce @f e2)

--coerce :: forall g1 g2 t. (CEmptyCtx g1, CEmptyCtx g2) => LExp g1 t -> LExp g2 t
--coerce e = transport e (emptyCtx @g1) (emptyCtx @g2)

coerce :: CEmptyCtx g => LExp g t -> LExp '[] t
coerce e = transportDown emptyCtx e


-- We've got some problems here.

-- instance Functor Lin where
--   -- f :: a -> b
--   -- a :: Lin a ~ Lift f (Lower a)
--   -- fmap f a :: Lift (Lower b)
--   fmap f (Lin a) = Lin (fmapLift f a)
-- instance Applicative Lin where
--   pure a = suspendL @'[] (put @'[] a)
--   -- a :: Lift (Lower a) 
--   -- f :: Lift (Lower (a -> b))
--   -- f <*> a :: Lift (Lower b)
--   Lin f <*> Lin a = Lin $ appLift f a
-- instance Monad Lin where
--   -- e :: Lin a = Lift (Lower a)
--   -- f :: a -> Lift (Lower b)
--   e >>= f  = suspendL @'[] $ forceL e >! \a -> forceL (f a)


-- force should also evaluate the expression
force :: forall t. Lift t -> LExp '[] t
-- e :: LExp g t
force (Suspend e) = coerce $ eval emptyCtx e

--forceL :: Lin a -> LExp '[] (Lower a)
-- forceL (Lin e) = _  where
--   e' = force e

suspend :: LExp '[] a -> Lift a
suspend = Suspend

suspendL :: forall g a. CEmptyCtx g => LExp g (Lower a) -> Lin a
suspendL = Lin . Suspend

evalC :: CEmptyCtx g => LExp g a -> LExp '[] a
evalC e = eval emptyCtx e

evalL :: Lin a -> Lin a
evalL (Lin e) = Lin $ evalL' e where
  evalL' :: forall a. Lift (Lower a) -> Lift (Lower a)
  evalL' (Suspend e) = Suspend $ eval (emptyCtx) e
