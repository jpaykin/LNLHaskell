{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase, RankNTypes, TypeFamilyDependencies
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
  type family (⊗) (s :: LType sig) (t :: LType sig) = (r :: LType sig) | r -> s t

data TensorExp :: forall sig. ExpDom sig where
  Pair :: forall sig (exp :: Ctx sig -> LType sig -> *) g1 g2 g t1 t2.
          HasTensorSig sig => Merge g1 g2 g
       -> exp g1 t1 -> exp g2 t2 -> TensorExp exp g (t1 ⊗ t2)
  LetPair :: forall sig (exp :: Ctx sig -> LType sig -> *) 
                    g1 g2 g2' g2'' g x1 x2 s1 s2 t.
             HasTensorSig sig 
          => Merge g1 g2'' g -> AddCtx x1 s1 g2'' g2' -> AddCtx x2 s2 g2' g2
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
  substDomain proxy pfA s (Pair pfM e1 e2) = 
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxy $ Pair pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxy $ Pair pfM2 e1 (subst pfA2 s e2)
  substDomain proxy pfA s (LetPair pfM pfA1 pfA2 e e') = undefined

  evalDomain _ (Pair pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      v1 <- eval' e1
      v2 <- eval' e2
      return $ vpair v1 v2
    }
  evalDomain proxy (LetPair pfM pfA1 pfA2 e e') = -- TODO: fix injectivity problem
    case mergeEmpty pfM of {Dict -> do
      Just (VPair v1 v2) <- fmap (fromLVal proxy) $ eval' e
      undefined
--      eval' $ subst pfA1 (valToExp v1) $ subst pfA2 (valToExp v2) e'
    }

  valToExpDomain _ (VPair v1 v2) = Pair MergeE (valToExp v1) (valToExp v2)

-- Lower -------------------------------------------------------

data LowerSig ty where
  LowerSig :: * -> LowerSig ty
class HasLowerSig sig where
  type Lower :: * -> LType sig

data LowerExp :: forall sig. ExpDom sig where
  Put :: a -> LowerExp exp 'Empty (Lower a)
  LetBang :: Merge g1 g2 g
          -> exp g1 (Lower a)
          -> (a -> exp g2 t)
          -> LowerExp exp g t
data LowerVal :: forall sig. ValDom sig where
  VPut :: a -> LowerVal val (Lower a)

proxyLower :: (Proxy LowerExp, Proxy LowerVal)
proxyLower = (Proxy,Proxy)

put :: InDom sig LowerExp LowerVal dom
    => a -> LExp dom 'Empty (Lower a)
put a = Dom proxyLower $ Put a

(>!) :: (InDom sig LowerExp LowerVal dom, CMerge g1 g2 g)
     => LExp dom g1 (Lower a)
     -> (a -> LExp dom g2 t)
     -> LExp dom g t
e >! f = Dom proxyLower $ LetBang merge e f

vput :: InDom sig LowerExp LowerVal dom
     => a -> LVal dom (Lower a)
vput a = VDom proxyLower $ VPut a

instance InDom sig LowerExp LowerVal dom 
      => Domain LowerExp LowerVal dom where
  substDomain _ pfA s (LetBang pfM e f) =
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxyLower $ LetBang pfM1 (subst pfA1 s e) f
      Right (pfA2,pfM2) -> Dom proxyLower $ LetBang pfM2 e f'
        where
          f' x = subst pfA2 s (f x)

  evalDomain _ (Put a) = return $ vput a
  evalDomain _ (LetBang pfM e f) = 
    case mergeEmpty pfM of {Dict -> do
      Just (VPut a) <- fmap (fromLVal proxyLower) $ eval' e
      eval' $ f a
    }

  valToExpDomain _ (VPut a) = Put a

-- concrete examples


type MultiplicativeProductSig = '[ OneSig, TensorSig ]
instance HasOneSig '(m,MultiplicativeProductSig) where
  type One = Sig' OneSig MultiplicativeProductSig 'OneSig
instance Monad m => HasTensorSig '(m,MultiplicativeProductSig) where
  type s ⊗ t = Sig' TensorSig MultiplicativeProductSig ('TensorSig s t)

--type MELL

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
