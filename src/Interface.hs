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

type SExp x s = LExp (FSingletonCtx x s) s

toSExp :: SIdent x -> SExp x s
toSExp x = Var $ fSingletonCtx x

var :: SIdent x -> SExp x t
var x = Var $ fSingletonCtx x


λ :: forall s t g g'. KnownCtx g
  => (LExp (FSingletonCtx (Fresh g) s) s -> LExp (FAddCtx (Fresh g) s g) t)
  -> LExp g (s ⊸ t)
λ f = Abs pfA (f varx) where
  pfA  = addFAdd ctx
  varx = var $ addToSIdent pfA



app :: CMerge g1 g2 g3 
    => LExp g1 (s ⊸ t)
    -> LExp g2 s
    -> LExp g3 t
e1 `app` e2 = App merge e1 e2

put :: a -> LExp  (Lower a)
put a = Put EmptyNil a

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

letPair :: forall g s1 s2 t g1 g2.
           (CIn (Fresh g) s1 g2, CIn (Fresh2 g) s2 g2
           ,CMerge g1 (Remove (Fresh g) (Remove (Fresh2 g) g2)) g
           ,KnownCtx g)
        => LExp g1 (s1 ⊗ s2)
        -> ( (SExp (Fresh g) s1, SExp (Fresh2 g) s2) -> LExp g2 t)
        -> LExp g t
letPair e f = LetPair merge pfA1 pfA2 e e'
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
    e' = f (toSExp $ addToSIdent pfA1, toSExp $ addToSIdent pfA2)

caseof :: forall g2 g g21 g22 g1 s1 s2 t.
          (CIn (Fresh g) s1 g21, CIn (Fresh g) s2 g22
          ,CAddCtx (Fresh g) s1 g2 g21
          ,CAddCtx (Fresh g) s2 g2 g22
          ,CMerge g1 g2 g
          ,KnownCtx g)
       => LExp g1 (s1 ⊕ s2)
       -> (SExp (Fresh g) s1 -> LExp g21 t)
       -> (SExp (Fresh g) s2 -> LExp g22 t)
       -> LExp g t
caseof e f1 f2 = Case merge pfA1 pfA2 e (f1 v1) (f2 v2)
  where
    pfA1 :: AddCtx (Fresh g) s1 g2 g21
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh g) s2 g2 g22
    pfA2 = addCtx
    v1 :: SExp (Fresh g) s1
    v1 = toSExp $ knownFresh (ctx @g)
    v2 :: SExp (Fresh g) s2
    v2 = toSExp $ knownFresh (ctx @g)


data Lift :: LType -> * where
  Suspend :: forall t. LExp '[] t -> Lift t




type Bang a = Lower (Lift a)
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
force (Suspend e) = eval emptyCtx e


forceL :: Lin a -> LExp '[] (Lower a)
forceL (Lin e) = force e

suspend :: CEmptyCtx g => LExp g a -> Lift a
suspend e = Suspend $ transportDown emptyCtx e

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

