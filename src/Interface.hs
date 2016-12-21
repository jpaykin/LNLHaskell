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
import Data.Proxy

import Types
import Context
import Proofs
import Classes
import Lang
import Subst
import Eval

type Var x s = SIdent x

var :: Var x s -> LExp sig (Singleton x s) s
var x = Var $ singSing x


-- DEFINING DOMAINS ---------------------------------

-- Abstraction and Application ----------------------

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


letin :: CMerge g1 g2 g
      => LExp sig g1 s
      -> LExp sig g2 (s ⊸ t)
      -> LExp sig g t
letin e f = f `app` e


{-
data LolliSig ty where
  LolliSig :: ty -> ty -> LolliSig ty

class HasLolli sig where
  type (⊸) (s :: LType sig) (t :: LType sig) :: LType sig

infixr 0 ⊸

instance CInList LolliSig (SigType sig) => HasLolli sig where
  type s ⊸ t = 'Sig PfInList ('LolliSig s t)

data LolliLExp :: ExpDom sig where
  Abs :: AddCtx x s g g'
      -> exp g' t
      -> LolliLExp exp g (s ⊸ t)
  App :: Merge g1 g2 g
      -> exp g1 (s ⊸ t)
      -> exp g2 s
      -> LolliLExp exp g t

data LolliLVal :: ValDom sig where
  VAbs :: AddCtx x s g g'
       -> 
-}
-- Combine signatures -----------------------

{-
data (:+:) :: TypeSig -> TypeSig -> TypeSig where
  AddSig1 :: ty1 (LType '(m,ty1)) -> (ty1 :+: ty2) (LType '(m, ty1 :+: ty2))
  AddSig2 :: ty2 a -> (ty1 :+: ty2) a



data Shape where
  NoShape :: Shape
  Shape0 :: Shape
  Shape1 :: Shape -> Shape
  Shape2 :: Shape -> Shape
data SShape (sh :: Shape) where
  SShape0 :: SShape Shape0
  SShape1 :: SShape sh -> SShape (Shape1 sh)

type family EitherShape (s1 :: Shape) (s2 :: Shape) :: Shape where
  EitherShape 'NoShape s2 = s2
  EitherShape s1       _  = s1
type family LookupShape (ty :: TypeSig) (sig :: Sig) where
  LookupShape ty '(m,ty)          = 'Shape0
  LookupShape ty '(m,ty1 :+: ty2) = 
    EitherShape (LookupShape ty '(m,ty1)) (LookupShape ty '(m,ty2))
  LookupShape ty '(m,_)           = 'NoShape

--type family LookupShape' (t :: ty (LType sig)) :: SigType sig (LType sig) 
--type instance LookupShape' ('AddSig1 
type family FromSingShape (s :: SShape sh) :: Shape where
  FromSingShape 'SShape0 = 'Shape0
  FromSingShape ('SShape1 s) = 'Shape1 (FromSingShape s)


data SSig m (ty :: TypeSig) (sig :: Sig) where
  SSig0 :: SSig m ty '(m,ty)
  SSig1 :: SSig m ty '(m,ty1) -> SSig m ty '(m,ty1 :+: ty2)
  SSig2 :: SSig m ty '(m,ty2) -> SSig m ty '(m,ty1 :+: ty2)

type family FromSSig (pf :: SSig m ty sig) :: Sig where
  FromSSig 'SSig0 = '(m,ty)

class InSig (ty :: TypeSig) (sig :: Sig) where
  type Inj (t :: ty (LType sig)) :: SigType sig (LType sig)

class InSig' (ty :: TypeSig) (sig :: Sig) where
  type SingSig :: SSig ty sig
  type Inj' sig (t :: ty (LType sig)) :: SigType sig (LType sig)

instance InSig' (LookupShape ty sig) ty sig => InSig ty sig where
  type Inj t = Inj' (FromSingShape SingShape) t

instance InSig' Shape0 ty '(m,ty) where
  type SingShape = SShape0
  type Inj' Shape0 t = t
instance InSig' sh ty '(m,sig1) => InSig' (Shape1 sh) ty '(m,sig1 :+: sig2) where
  type SingShape = SShape1 SingShape
  type Inj' (Shape1 sh) t = 'AddSig1 (Inj' sh t)
-}
{-
instance InSig' 0 ty '(m,ty) where
  type Inj' 0 t = t
instance InSig ty '(m,ty1) => InSig' 1 ty '(m, ty1 :+: ty2) where
  type Inj' 1 t = 'AddSig1 (Inj t)
-}

--instance InSig 0 ty '(m,ty) where
--  type Inj t = t
--instance InSig 0 ty '(m,ty1) => InSig 1 ty '(m,ty1 :+: ty2) where
--  type Inj t = 'AddSig1 t
-- instance InSig 1 ty '(m,ty1) => InSig 1 ty '(m,ty1 :+: ty2)
-- instance InSig 2 ty '(m,ty1) => InSig 1 ty '(m,ty1 :+: ty2)
-- instance InSig 0 ty '(m,ty2) => InSig 2 ty '(m,ty1 :+: ty2)
-- instance InSig 1 ty '(m,ty2) => InSig 2 ty '(m,ty1 :+: ty2)
-- instance InSig 2 ty '(m,ty2) => InSig 2 ty '(m,ty1 :+: ty2)


-- One ---------------------------------------
-- GOAL: have types that don't have to be indexed by the signature.

data OneSig ty where
  OneSig :: OneSig ty
class HasOneSig sig where
  type One :: LType sig
-- Instances need to be declared for each concrete signature
--instance CInSig OneSig sig => HasOne sig where
--  type One = 'Sig (PfInList :: InList OneSig (SigType sig)) 'OneSig


data OneExp :: forall sig. ExpDom sig where
  Unit :: forall sig (exp :: Ctx sig -> LType sig -> *).
          HasOneSig sig => OneExp exp 'Empty One
  LetUnit :: forall sig (exp :: Ctx sig -> LType sig -> *) 
                   (g :: Ctx sig) (g1 :: Ctx sig) (g2 :: Ctx sig) (t :: LType sig).
            HasOneSig sig
         => Merge g1 g2 g -> exp g1 One -> exp g2 t -> OneExp exp g t

data OneVal :: forall sig. ValDom sig where
  VUnit :: forall sig (val :: LType sig -> *).
           HasOneSig sig => OneVal val One
{-
class (WellScopedDom sig dom, HasOneSig sig, CInList '(OneExp,OneVal) dom) 
   => HasOne sig (dom :: Dom sig)
instance (WellScopedDom sig dom, HasOneSig sig, CInList '(OneExp,OneVal) dom) 
      => HasOne sig dom
-}
proxyOne :: (Proxy OneExp, Proxy OneVal)
proxyOne = (Proxy,Proxy)

unit :: (HasOneSig sig, InDom sig OneExp OneVal dom)
     => LExp dom 'Empty One
unit = Dom proxyOne Unit
letUnit :: (HasOneSig sig, InDom sig OneExp OneVal dom, CMerge g1 g2 g)
        => LExp dom g1 One -> LExp dom g2 t -> LExp dom g t
letUnit e1 e2 = Dom proxyOne $ LetUnit merge e1 e2

vunit :: (HasOneSig sig, InDom sig OneExp OneVal dom)
      => LVal dom One
vunit = VDom proxyOne VUnit

instance (HasOneSig sig, InDom sig OneExp OneVal dom) => Domain OneExp OneVal dom where
  substDomain _ pfA s (LetUnit pfM e1 e2) = 
    case mergeAddSplit pfM pfA of 
      Left  (pfA1,pfM1) -> Dom proxyOne $ LetUnit pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxyOne $ LetUnit pfM2 e1 (subst pfA2 s e2)

  evalDomain _ Unit = return vunit
  evalDomain proxy (LetUnit pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      Just VUnit <- fmap (fromLVal proxy) $ eval' e1
      eval' e2
    }

  valToExpDomain _ VUnit = Unit

-- Tensor ------------------------------------------------------

data TensorSig ty = TensorSig ty ty
class HasTensorSig sig where
  type (⊗) (s :: LType sig) (t :: LType sig) :: LType sig

data TensorExp :: forall sig. ExpDom sig where
  Pair :: forall sig (exp :: Ctx sig -> LType sig -> *) g1 g2 g t1 t2.
          HasTensorSig sig => Merge g1 g2 g
       -> exp g1 t1 -> exp g2 t2 -> TensorExp exp g (t1 ⊗ t2)
  LetPair :: forall sig (exp :: Ctx sig -> LType sig -> *) g1 g2 g2' g2'' g x1 x2 s1 s2 t.
             HasTensorSig sig => Merge g1 g2'' g -> AddCtx x1 s1 g2'' g2' -> AddCtx x2 s2 g2' g2
          -> exp g1 (s1 ⊗ s2) -> exp g2 t -> TensorExp exp g t
data TensorVal :: forall sig. ValDom sig where
  VPair :: forall sig (val :: LType sig -> *) t1 t2.
           HasTensorSig sig 
        => val t1 -> val t2 -> TensorVal val (t1 ⊗ t2)

proxyTensor :: (Proxy TensorExp, Proxy TensorVal)
proxyTensor = (Proxy,Proxy)

(⊗) :: (HasTensorSig sig, InDom sig TensorExp TensorVal dom, CMerge g1 g2 g)
     => LExp dom g1 s1 -> LExp dom g2 s2 -> LExp dom g (s1 ⊗ s2)
e1 ⊗ e2 = Dom proxyTensor $ Pair merge e1 e2

letPair :: forall sig (dom :: Dom sig) g g1 g2 g2' g2'' s1 s2 t.
         ( HasTensorSig sig, InDom sig TensorExp TensorVal dom
         , CAddCtx (Fresh g) s1 g2'' g2'
         , CAddCtx (Fresh2 g) s2 g2' g2
         , CMerge g1 g2'' g)
        => LExp dom g1 (s1 ⊗ s2)
        -> ((Var (Fresh g) s1, Var (Fresh2 g) s2) -> LExp dom g2 t)
        -> LExp dom g t
letPair e f = Dom proxyTensor $ LetPair pfM pfA1 pfA2 e e'
  where
    pfM :: Merge g1 g2'' g
    pfM = merge
    pfA1 :: AddCtx (Fresh g) s1 g2'' g2'
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh2 g) s2 g2' g2
    pfA2 = addCtx

    e' :: LExp dom g2 t
    e' = f (knownFresh g, knownFresh2 g)
    g :: SCtx g
    (_,_,g) = mergeSCtx pfM

vpair :: (HasTensorSig sig, InDom sig TensorExp TensorVal dom) 
      => LVal dom s1 -> LVal dom s2 -> LVal dom (s1 ⊗ s2)
vpair v1 v2 = VDom proxyTensor $ VPair v1 v2


instance (HasTensorSig sig, InDom sig TensorExp TensorVal dom)
      => Domain TensorExp TensorVal dom where
  substDomain = undefined
  evalDomain = undefined
  valToExpDomain = undefined

newtype Id a = Id a

-- concrete examples

type MultiplicativeProductSig = '[ OneSig, TensorSig ]
instance HasOneSig '(m,MultiplicativeProductSig) where
  type One = Sig' OneSig MultiplicativeProductSig 'OneSig
instance HasTensorSig '(m,MultiplicativeProductSig) where
  type s ⊗ t = Sig' TensorSig MultiplicativeProductSig ('TensorSig s t)


{-

put :: a -> LExp sig 'Empty (Lower a)
put = Put

(>!) :: CMerge g1 g2 g3
     => LExp sig g1 (Lower a)
     -> (a -> LExp sig g2 t)
     -> LExp sig g3 t
(>!) = LetBang merge


(&) :: LExp sig g t1
    -> LExp sig g t2
    -> LExp sig g (t1 & t2)
(&) = Prod





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
    
    
-}
