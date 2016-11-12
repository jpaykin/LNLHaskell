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

-- type Var x s = LExp (Singleton x s) s
type Var x s = SIdent x

var :: Var x s -> LExp (Singleton x s) s
var x = Var $ singSing x


λ :: forall s t g g'. CAddCtx (Fresh g) s g g'
  => (Var (Fresh g) s -> LExp g' t)
  -> LExp g (s ⊸ t)
λ f = Abs pfA (f x) where
  pfA :: AddCtx (Fresh g) s g g'
  pfA  = addCtx
  x   :: SIdent (Fresh g)
  x    = addToSIdent pfA

app :: CMerge g1 g2 g3 
    => LExp g1 (s ⊸ t)
    -> LExp g2 s
    -> LExp g3 t
e1 `app` e2 = App merge e1 e2

put :: a -> LExp 'Empty (Lower a)
put = Put

(>!) :: CMerge g1 g2 g3
     => LExp g1 (Lower a)
     -> (a -> LExp g2 t)
     -> LExp g3 t
(>!) = LetBang merge

(⊗) :: CMerge g1 g2 g3
    => LExp g1 t1
    -> LExp g2 t2
    -> LExp g3 (t1 ⊗ t2)
e1 ⊗ e2 = Pair merge e1 e2

(&) :: LExp g t1
    -> LExp g t2
    -> LExp g (t1 & t2)
(&) = Prod

letUnit :: CMerge g1 g2 g
        => LExp g1 One -> LExp g2 t -> LExp g t
letUnit = LetUnit merge


letPair :: forall g s1 s2 t g1 g2 g2' g2''.
           ( CAddCtx (Fresh g) s1 g2'' g2'
           , CAddCtx (Fresh2 g) s2 g2' g2
           , CMerge g1 g2'' g)
        => LExp g1 (s1 ⊗ s2)
        -> ((Var (Fresh g) s1, Var (Fresh2 g) s2) -> LExp g2 t)
        -> LExp g t
letPair = undefined

{-
letPair :: forall g s1 s2 t g1 g2 g2' g2''.
           (CIn (Fresh g) s1 g2, CIn (Fresh2 g) s2 g2
           ,CRemoveCtx (Fresh2 g) s2 g2 g2', CRemoveCtx (Fresh g) s1 g2' g2''
           ,CMerge g1 g2'' g
           ,KnownCtx g
           )
        => LExp g1 (s1 ⊗ s2)
        -> ((Var (Fresh g) s1, Var (Fresh2 g) s2) -> LExp g2 t)
        -> LExp g t
letPair e f = 
    case addRemoveEquiv (removeCtx @(Fresh2 g) @s2 @g2 @g2') of {Dict ->
    case addRemoveEquiv (removeCtx @(Fresh g) @s1 @g2' @g2'') of {Dict ->
    LetPair (merge @g1 @g2'' @g) pfA1 pfA2 e e'
    }}
  where
    pfI1 :: In (Fresh g) s1 g2
    pfI1 = inCtx
    pfI1' :: In (Fresh g) s1 (Remove (Fresh2 g) g2)
    pfI1' = disjointRemove (freshDisjoint (ctx @g)) pfI1 pfI2
    pfI2 :: In (Fresh2 g) s2 g2
    pfI2 = inCtx
    pfA1 :: AddCtx (Fresh g) s1 (Remove (Fresh g) (Remove (Fresh2 g) g2)) (Remove (Fresh2 g) g2)
    pfA1 = inAddRemove pfI1'
    pfA2 :: AddCtx (Fresh2 g) s2 (Remove (Fresh2 g) g2) g2
    pfA2 = inAddRemove pfI2
    e' :: LExp g2 t
    e' = f (addToSIdent pfA1, addToSIdent pfA2)
-}

caseof :: forall g2 g g21 g22 g1 s1 s2 t.
          (CIn (Fresh g) s1 g21, CIn (Fresh g) s2 g22
          ,CAddCtx (Fresh g) s1 g2 g21
          ,CAddCtx (Fresh g) s2 g2 g22
          ,CMerge g1 g2 g
          ,KnownCtx g)
       => LExp g1 (s1 ⊕ s2)
       -> (Var (Fresh g) s1 -> LExp g21 t)
       -> (Var (Fresh g) s2 -> LExp g22 t)
       -> LExp g t
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

-- Lift --------------------------------------------------------

data Lift :: LType -> * where
  Suspend :: forall t. LExp 'Empty t -> Lift t

-- force should also evaluate the expression
force :: forall t. Lift t -> LExp 'Empty t
force (Suspend e) = eval e



-- Linearity Monad and Comonad -------------------------------

type Bang a = Lower (Lift a)
data Lin a where
  Lin :: Lift (Lower a) -> Lin a



instance Functor Lin where
  -- f :: a -> b
  -- a :: Lin a ~ Lift f (Lower a)
  -- fmap f a :: Lift (Lower b)
  fmap f (Lin (Suspend e)) = Lin . Suspend $ e >! \ x → put (f x)
instance Applicative Lin where
  pure a = Lin $ Suspend (put a)
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



forceL :: Lin a -> LExp 'Empty (Lower a)
forceL (Lin e) = force e

suspendL :: LExp 'Empty (Lower a) -> Lin a
suspendL = Lin . Suspend 

evalL :: Lin a -> Lin a
evalL (Lin e) = Lin $ evalL' e where
  evalL' :: forall a. Lift (Lower a) -> Lift (Lower a)
  evalL' (Suspend e) = Suspend $ eval e

evalVal :: Lin a -> LVal (Lower a) 
evalVal (Lin (Suspend e)) = eval' e

run :: Lin a -> a
run e = case evalVal e of VPut a -> a

