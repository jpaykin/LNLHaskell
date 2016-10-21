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
import Frame
import FrameClass
import Lang

var :: forall x f1 f2 t g. CSingletonCtx x t f1 f2 g 
    => LExp (Splice f1 x f2) g t
var = Var (singletonCtx @x @t @f1 @f2)

λ :: forall x f1 f2 s t g g'. CAddCtx x s f1 f2 g g' 
  => LExp (Splice f1 x f2) g' t 
  -> LExp (Splice f1 x f2) g (s ⊸ t)
λ t = Abs (addCtx @x @_ @f1 @f2) t

(@@) :: CMerge g1 g2 g3 
    => LExp f g1 (s ⊸ t)
    -> LExp f g2 s
    -> LExp f g3 t
e1 @@ e2 = App merge e1 e2

put :: forall (f::Frame) (g::Ctx) a. CEmptyCtx f g => a -> LExp f g (Lower a)
put a = Put (emptyCtx @f @g) a

(>!) :: CMerge g1 g2 g3
     => LExp f g1 (Lower a)
     -> (a -> LExp f g2 t)
     -> LExp f g3 t
(>!) = LetBang merge


data Lift :: Frame -> LType -> * where
  Suspend :: forall f g t. CEmptyCtx f g => LExp f g t -> Lift f t


data Lin a where
  Lin :: forall f a. Lift f (Lower a) -> Lin a


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

coerce :: forall f g1 g2 t. (CEmptyCtx f g1, CEmptyCtx f g2) => LExp f g1 t -> LExp f g2 t
coerce e = case emptyUnique (emptyCtx @f @g1) (emptyCtx @f @g2) of
             Dict -> e


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
force :: forall f g t. CEmptyCtx f g => Lift f t -> LExp f g t
-- e :: LExp g t
force (Suspend e) = coerce @f $ eval (emptyCtx @f) e

--forceL :: Lin a -> LExp '[] (Lower a)
-- forceL (Lin e) = _  where
--   e' = force e

suspend :: forall f g a. CEmptyCtx f g => LExp f g a -> Lift f a
suspend = Suspend

suspendL :: forall f g a. CEmptyCtx f g => LExp f g (Lower a) -> Lin a
suspendL = Lin . Suspend @f 

evalL :: Lin a -> Lin a
evalL (Lin e) = Lin $ evalL' e where
  evalL' :: forall f a. Lift f (Lower a) -> Lift f (Lower a)
  evalL' (Suspend e) = Suspend @f $ eval (emptyCtx @f) e

