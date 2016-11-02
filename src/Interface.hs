{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase, TypeFamilyDependencies
#-}

module Interface where

import Data.Kind
import Data.Constraint

import Types
import Context
import Classes
import Proofs
import Lang
import Subst

-- var :: forall x g t. CSingletonCtx x t g 
--     => LExp g t
-- var = Var (singletonCtx @x @t)

var :: NatS x -> LExp (Sing x s) s
var x = Var $ singS x

λ :: forall s t g g'. (KnownCtx g, CAddCtx (FreshCtx g) s g g')
  => (LExp (Sing (FreshCtx g) s) s -> LExp g' t)
  -> LExp g (s ⊸ t)
λ f = Abs pfA (f varx) where
  pfA  = addCtx @(FreshCtx g) @s @g @g'
  varx = var $ addToNatS pfA

app :: CMerge g1 g2 g3 
    => LExp g1 (s ⊸ t)
    -> LExp g2 s
    -> LExp g3 t
e1 `app` e2 = App merge e1 e2


-- (⊗) :: CMerge g1 g2 g3
--     => LExp g1 s
--     -> LExp g2 t
--     -> LExp g3 (s ⊗ t)
-- e1 ⊗ e2 = Pair merge e1 e2


letpair :: forall x y g2 s t g1 g3 g2' g2'' r.
           (CMerge g1 g2 g3, CAddCtx x s g2 g2', CAddCtx y t g2' g2'')
        => LExp g1 (s ⊗ t)
        -> LExp g2'' r
        -> LExp g3 r
letpair e1 e2 = LetPair (merge @g1 @g2 @g3) (addCtx @x) (addCtx @y) e1 e2

put :: a -> LExp '[] (Lower a)
put a = Put EmptyNil a

(>!) :: CMerge g1 g2 g3
     => LExp g1 (Lower a)
     -> (a -> LExp g2 t)
     -> LExp g3 t
(>!) = LetBang merge

-- tuples

tup :: LExps g ts
    -> LExp g (Tuple ts)
tup = ETuple

(.:) :: CMerge g1 g2 g3 => LExp g1 t -> LExps g2 ts -> LExps g3 (t ': ts)
e1 .: e2 = LExpCons merge e1 e2

(.&) :: CMerge g1 g2 g3 => LExp g1 t1 -> LExp g2 t2 -> LExps g3 '[ t1, t2 ]
e1 .& e2 = LExpCons merge e1 (LExpCons MergeER e2 LExpNil)

-- tup $ e1 .: e2 .& e3

type family FromPat p s = result where
  FromPat (PVar x)    s          = LExp (Sing x s) s
  FromPat (PTuple ps) (Tuple ts) = FromPats ps ts

type family FromPats ps ts = result where
  FromPats '[]                 _                   = ()
  FromPats '[ p ]              '[ t ]              = FromPat p t
  FromPats '[ p1, p2 ]         '[ t1, t2 ]         = (FromPat p1 t1, FromPat p2 t2)
  FromPats '[ p1, p2, p3 ]     '[ t1, t2, t3 ]     = 
    (FromPat p1 t1, FromPat p2 t2, FromPat p3 t3)
  FromPats '[ p1, p2, p3, p4 ] '[ t1, t2, t3, t4 ] = 
    (FromPat p1 t1, FromPat p2 t2, FromPat p3 t3, FromPat p4 t4)
  FromPats (p ': ps)            (t ': ts)          = (FromPat p t, FromPats ps ts)


type family FreshPat g s :: Pattern where
  FreshPat g (Tuple ts) = PTuple (FreshPats g ts)
  FreshPat g s          = PVar (FreshCtx g)
--  FreshPat g (PTuple ps) = FreshPats g ps

type family FreshPats g ts :: [Pattern] where
  FreshPats g '[] = '[]
  FreshPats g (t ': ts) = FreshPat g t ': FreshPats (AddPatFun (FreshPat g t) t g) ts

-- type family AddLTypes ts g :: Ctx where
--   AddLTypes '[] g = g
--   AddLTypes (t ': ts) g = AddLType t (AddLTypes ts g)

-- type family AddLType t g :: Ctx where
--   AddLType t '[] = '[ 'Used t ]
--   AddLType t ('Unused ': g) = 'Used t ': g
--   AddLType t ('Used s ': g) = 'Used s ': AddLType t g

-- type SingLTypes ts = AddLTypes ts '[]

caseof' :: forall g1 g2 g2' g ts t.
          (CMerge g1 g2 g, CSingletonLTypes ts g, CAddLTypes ts g2 g2')
       => LExp g1 (Tuple ts)
       -> (LExps g ts -> LExp g2' t)
       -> LExp g t
caseof' e f = Case (merge @g1 @g2) pfA e e' 
  where
    pfA = undefined
    e'  = f $ mkLTypePats singletonLTypes

mkLTypePats :: AddLTypes ts '[] g -> LExps g ts
mkLTypePats (AddLsNil) = LExpNil
mkLTypePats (AddLsCons pfA pfAs) = undefined -- LExpCons _ (mkLTypePat pfA) (mkLTypePats pfAs)

mkLTypePat :: AddLType t '[] g -> LExp g t
mkLTypePat = undefined



caseof :: forall g1 g2 g3 s t.
          (CMerge g1 (RemovePat (FreshPat g1 s) g2) g3, CInPat (FreshPat g1 s) s g2)
       => LExp g1 s
       -> (FromPat (FreshPat g1 s) s -> LExp g2 t)
       -> LExp g3 t
caseof e f = undefined -- Case merge _ e (f . freshPat @_ @s $ freshPatKnown @g1 @s)

-- freshPatKnown :: SPat (FreshPat g t)
-- freshPatKnown = undefined

-- mkPat :: forall p t. SPat p -> FromPat p t
-- mkPat (MkVar x)    = var x
-- mkPat (MkTuple ps) = mkPats @t ps

-- mkPats :: SPats ps -> FromPats ps ts
-- mkPats MkNil            = ()
-- mkPats (MkCons p MkNil) = mkPat p


-- caseof :: forall p s t g1 g2 g3.
--           (CMerge g1 (RemovePat p g2) g3, CInPat p s g2)
--        => LExp g1 s
--        -> LExp g2 t
--        -> LExp g3 t
-- caseof e1 e2 =  undefined -- Case (merge) (addPat @p) e1 e2

-- match :: forall g1 g2 g2' g3 p s t. (CAddPat p s g2 g2', CMerge2 g1 g2 g3) 
--       => SPat p -> LExp g1 s -> LExp g2' t -> LExp g3 t
-- match = undefined

-- patExp :: SPat p -> AddPat p s '[] g' -> LExp g' s
-- patExp = undefined

-- mkPat :: forall s g' p. CAddPat p s '[] g' => SPat p -> LExp g' s
-- mkPat p = patExp p addPat


data Lift :: LType -> * where
  Suspend :: forall t. LExp '[] t -> Lift t


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
run e = fromVPut $ evalVal e
