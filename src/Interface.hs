{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase, RankNTypes
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
import Eval

-- type Var x s = LExp (Singleton x s) s
type Var x s = SIdent x

var :: Var x s -> LExp sig (Singleton x s) s
var x = Var $ singSing x

λ :: forall sig s t g g'. CAddCtx (Fresh g) s g g'
  => (Var (Fresh g) s -> LExp sig g' t)
  -> LExp sig g (s ⊸ t)
λ f = Abs pfA (f x) where
  pfA :: AddCtx (Fresh g) s g g'
  pfA  = addCtx
  x   :: SIdent (Fresh g)
  x    = addToSIdent pfA

app :: CMerge g1 g2 g3 
    => LExp sig g1 (s ⊸ t)
    -> LExp sig g2 s
    -> LExp sig g3 t
e1 `app` e2 = App merge e1 e2

put :: a -> LExp sig 'Empty (Lower a)
put = Put

(>!) :: CMerge g1 g2 g3
     => LExp sig g1 (Lower a)
     -> (a -> LExp sig g2 t)
     -> LExp sig g3 t
(>!) = LetBang merge

(⊗) :: CMerge g1 g2 g3
    => LExp sig g1 t1
    -> LExp sig g2 t2
    -> LExp sig g3 (t1 ⊗ t2)
e1 ⊗ e2 = Pair merge e1 e2

(&) :: LExp sig g t1
    -> LExp sig g t2
    -> LExp sig g (t1 & t2)
(&) = Prod

letin :: (CMerge g1 g2 g, CMergeForward g2 g1 g, CDiv g g1 g2, CDiv g g2 g1)
      => LExp sig g1 s
      -> LExp sig g2 (s ⊸ t)
      -> LExp sig g t
letin e f = f `app` e

letUnit :: CMerge g1 g2 g
        => LExp sig g1 One -> LExp sig g2 t -> LExp sig g t
letUnit = LetUnit merge


letPair :: forall sig g s1 s2 t g1 g2 g2' g2''.
           ( CAddCtx (Fresh g) s1 g2'' g2'
           , CAddCtx (Fresh2 g) s2 g2' g2
           , CMerge g1 g2'' g)
        => LExp sig g1 (s1 ⊗ s2)
        -> ((Var (Fresh g) s1, Var (Fresh2 g) s2) -> LExp sig g2 t)
        -> LExp sig g t
letPair e f = 
    case addRemoveEquiv (removeCtx @(Fresh2 g) @s2 @g2 @g2') of {Dict ->
    case addRemoveEquiv (removeCtx @(Fresh g) @s1 @g2' @g2'') of {Dict ->
    LetPair (merge @g1 @g2'' @g) pfA1 pfA2 e e'
    }}
  where
    g    :: SCtx g
    (_,_,g) = mergeSCtx (merge @g1 @g2'' @g)
    x1   :: SIdent (Fresh g)
    x1   = knownFresh g
    x2   :: SIdent (Fresh2 g)
    x2   = knownFresh2 g
    pfI0 :: In (Fresh g) s1 g2'
    pfI0 = addIn $ addCtx @(Fresh g) @s1 @g2'' @g2'
    pfI1 :: In (Fresh g) s1 g2
    pfI1 = inAdd pfI0 $ addCtx @(Fresh2 g) @s2 @g2' @g2
    pfI1' :: In (Fresh g) s1 (Remove (Fresh2 g) g2)
    pfI1' = disjointRemove (freshDisjoint g) pfI1 pfI2
    pfI2 :: In (Fresh2 g) s2 g2
    pfI2 = addIn $ addCtx @(Fresh2 g) @s2 @g2' @g2
    pfA1 :: AddCtx (Fresh g) s1 (Remove (Fresh g) (Remove (Fresh2 g) g2)) (Remove (Fresh2 g) g2)
    pfA1 = inAddRemove pfI1'
    pfA2 :: AddCtx (Fresh2 g) s2 (Remove (Fresh2 g) g2) g2
    pfA2 = inAddRemove pfI2
    e' :: LExp sig g2 t
    e' = f (x1,x2)


caseof :: forall sig g2 g g21 g22 g1 s1 s2 t.
          (CIn (Fresh g) s1 g21, CIn (Fresh g) s2 g22
          ,CAddCtx (Fresh g) s1 g2 g21
          ,CAddCtx (Fresh g) s2 g2 g22
          ,CMerge g1 g2 g
          ,KnownCtx g)
       => LExp sig g1 (s1 ⊕ s2)
       -> (Var (Fresh g) s1 -> LExp sig g21 t)
       -> (Var (Fresh g) s2 -> LExp sig g22 t)
       -> LExp sig g t
caseof e f1 f2 = Case merge pfA1 pfA2 e (f1 v1) (f2 v2)
  where
    pfA1 :: AddCtx (Fresh g) s1 g2 g21
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh g) s2 g2 g22
    pfA2 = addCtx
    v1 :: Var (Fresh g) s1
    v1 = knownFresh (ctx @g)
    v2 :: Var (Fresh g) s2
    v2 = knownFresh (ctx @g)




-- Linearity Monad and Comonad -------------------------------

type family Bang (dom :: Dom sig) (a :: LType sig) :: LType sig where
  Bang dom a = Lower (Lift dom a)
data Lin dom a where
  Lin :: Lift dom (Lower a) -> Lin dom a



instance Functor (Lin dom) where
  -- f :: a -> b
  -- a :: Lin a ~ Lift f (Lower a)
  -- fmap f a :: Lift (Lower b)
  fmap f (Lin (Suspend e)) = Lin . Suspend $ e >! \ x → put (f x)
instance Applicative (Lin dom) where
  pure a = Lin $ Suspend (put a)
  -- a :: Lift (Lower a) 
  -- f :: Lift (Lower (a -> b))
  -- f <*> a :: Lift (Lower b)
  Lin (Suspend f) <*> Lin (Suspend e) = Lin . Suspend $ e >! \ x -> 
                                                        f >! \ f' -> 
                                                        put (f' x)
instance Monad (Lin dom) where
  -- e :: Lin a = Lift (Lower a)
  -- f :: a -> Lift (Lower b)
  Lin (Suspend e) >>= f  = Lin . Suspend $ e >! \ x -> forceL (f x)



forceL :: Lin dom a -> LExp dom 'Empty (Lower a)
forceL (Lin e) = force e

suspendL :: LExp dom 'Empty (Lower a) -> Lin dom a
suspendL = Lin . Suspend 

evalL :: forall sig (dom :: Dom sig) a.
         Monad (SigEffect sig) => Lin dom a -> SigEffect sig (Lin dom a)
evalL (Lin e) = fmap Lin $ evalL' e where
  evalL' :: forall sig (dom :: Dom sig) a. Monad (SigEffect sig) 
         => Lift dom (Lower a) -> SigEffect sig (Lift dom (Lower a))
  evalL' (Suspend e) = fmap Suspend $ eval e

evalVal :: forall sig (dom :: Dom sig) a. Monad (SigEffect sig) 
        => Lin dom a -> SigEffect sig (LVal dom (Lower a))
evalVal (Lin (Suspend e)) = eval' e

run :: forall sig (dom :: Dom sig) a. Monad (SigEffect sig) 
    => Lin dom a -> SigEffect sig a
run e = do
  VPut a <- evalVal e
  return a

-- Monads in the linear fragment ----------------------------------

class LFunctor (f :: LType sig -> LType sig) where
  lfmap :: LExp dom 'Empty ((s ⊸ t) ⊸ f s ⊸ f t)
class LFunctor f => LApplicative (f :: LType sig -> LType sig) where
  lpure :: LExp dom 'Empty (s ⊸ f s)
  llift :: LExp dom 'Empty (f(s ⊸ t) ⊸ f s ⊸ f t)
class LApplicative m => LMonad (m :: LType sig -> LType sig) where
  lbind :: LExp dom 'Empty ( m s ⊸ (s ⊸ m t) ⊸ m t)

lowerT :: (a -> b) -> LExp dom 'Empty (Lower a ⊸ Lower b)
lowerT f = λ $ \x -> 
  var x >! \ a ->
  put $ f a

liftT :: LExp dom 'Empty (s ⊸ t) -> Lift dom s -> Lift dom t
liftT f e = Suspend $ f `app` force e

data LinT dom (f :: LType sig -> LType sig) a where
  LinT :: Lift dom (f (Lower a)) -> LinT dom f a

forceT :: LinT dom f a -> LExp dom 'Empty (f (Lower a))
forceT (LinT e) = force e

instance LFunctor f => Functor (LinT dom f) where
  fmap :: (a -> b) -> LinT dom f a -> LinT dom f b
  fmap f (LinT e) = LinT . Suspend $ lfmap `app` lowerT f `app` force e

instance LApplicative f => Applicative (LinT dom f) where
  pure :: a -> LinT dom f a
  pure a = LinT . Suspend $ lpure `app` put a

  (<*>) :: LinT dom f (a -> b) -> LinT dom f a -> LinT dom f b
  LinT f <*> LinT a = LinT . Suspend $ 
    llift `app` (lfmap `app` lowerT' `app` force f) `app` force a
    where
      lowerT' :: LExp dom 'Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
      lowerT' = λ $ \gl ->
                  var gl >! \g ->
                  lowerT g

instance LMonad m => Monad (LinT dom m) where
  (>>=) :: forall dom a b. 
           LinT dom m a -> (a -> LinT dom m b) -> LinT dom m b
  LinT ma >>= f = LinT . Suspend $ lbind `app` force ma `app` f'
    where
      f' :: LExp dom 'Empty (Lower a ⊸ m (Lower b))
      f' = λ $ \la ->
        var la >! \a ->
        forceT $ f a
    
    
