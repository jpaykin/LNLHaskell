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
import Data.Singletons
--import Control.Category

import Types
import Context
import Proofs
import Classes
import Lang

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


letin :: CMerge g1 g2 g
      => LExp sig g1 s
      -> LExp sig g2 (s ⊸ t)
      -> LExp sig g t
letin e f = f `app` e

-- Categories ----------------------------

--newtype LArrow (dom :: Dom sig) (s :: LType sig) (t :: LType sig) = LArrow (LExp dom 'Empty (s ⊸ t))

--instance Category (LArrow dom) where
--  id    = LArrow $ λ var
--  LArrow g . LArrow f = LArrow Prelude.. λ $ \x -> g `app` (f `app` var x)

-- DEFINING DOMAINS ---------------------------------

-- Abstraction and Application ----------------------


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

type One = ('Sig (InSig OneSig sig) 'OneSig :: LType sig)

data OneExp :: forall sig. ExpDom sig where
  Unit :: OneExp exp 'Empty One
  LetUnit :: Merge g1 g2 g -> exp g1 One -> exp g2 t -> OneExp exp g t

data OneVal :: forall sig. ValDom sig where
  VUnit :: OneVal val One

type OneDom = '(OneExp,OneVal)

proxyOne :: Proxy OneDom
proxyOne = Proxy

unit :: Domain OneDom lang
     => LExp lang 'Empty One
unit = Dom proxyOne Unit

letUnit :: (Domain OneDom lang, CMerge g1 g2 g)
        => LExp lang g1 One -> LExp lang g2 t -> LExp lang g t
letUnit e1 e2 = Dom proxyOne $ LetUnit merge e1 e2

vunit :: Domain OneDom lang
      => LVal lang One
vunit = VDom proxyOne VUnit

instance Domain OneDom lang
      => Language OneDom lang where
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

type (⊗) (s :: LType sig) (t :: LType sig) = 
     'Sig (InSig TensorSig sig) ('TensorSig s t)

data TensorExp :: forall sig. ExpDom sig where
  Pair :: Merge g1 g2 g
       -> exp g1 t1 -> exp g2 t2 -> TensorExp exp g (t1 ⊗ t2)
  LetPair :: Merge g1 g2'' g -> AddCtx x1 s1 g2'' g2' -> AddCtx x2 s2 g2' g2
          -> exp g1 (s1 ⊗ s2) -> exp g2 t -> TensorExp exp g t
data TensorVal :: forall sig. ValDom sig where
  VPair :: val t1 -> val t2 -> TensorVal val (t1 ⊗ t2)

type TensorDom  = '(TensorExp, TensorVal)

proxyTensor :: Proxy TensorDom
proxyTensor = Proxy

(⊗) :: forall sig lang g1 g2 g s1 s2.
       (Domain TensorDom lang, CMerge g1 g2 g)
     => LExp lang g1 s1 -> LExp lang g2 s2 -> LExp lang g (s1 ⊗ s2)
e1 ⊗ e2 = Dom proxyTensor $ Pair merge e1 e2

letPair :: forall sig (lang :: Lang sig) g g1 g2 g2' g2'' s1 s2 t.
         ( Domain TensorDom lang
         , CAddCtx (Fresh g) s1 g2'' g2'
         , CAddCtx (Fresh2 g) s2 g2' g2
         , CMerge g1 g2'' g)
        => LExp lang g1 (s1 ⊗ s2)
        -> ((Var (Fresh g) s1, Var (Fresh2 g) s2) -> LExp lang g2 t)
        -> LExp lang g t
letPair e f = Dom proxyTensor $ LetPair pfM pfA1 pfA2 e e'
  where
    pfM :: Merge g1 g2'' g
    pfM = merge
    pfA1 :: AddCtx (Fresh g) s1 g2'' g2'
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh2 g) s2 g2' g2
    pfA2 = addCtx

    e' :: LExp lang g2 t
    e' = f (knownFresh g, knownFresh2 g)
    g :: SCtx g
    (_,_,g) = mergeSCtx pfM

vpair :: Domain TensorDom lang
      => LVal lang s1 -> LVal lang s2 -> LVal lang (s1 ⊗ s2)
vpair v1 v2 = VDom proxyTensor $ VPair v1 v2



instance Domain TensorDom lang
      => Language TensorDom lang where
  substDomain proxy pfA s (Pair pfM e1 e2) = 
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxy $ Pair pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxy $ Pair pfM2 e1 (subst pfA2 s e2)
  substDomain proxy pfA s (LetPair pfM pfA1 pfA2 e e') = undefined -- TODO

  evalDomain _ (Pair pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      v1 <- eval' e1
      v2 <- eval' e2
      return $ vpair v1 v2
    }
  evalDomain proxy (LetPair pfM pfA1 pfA2 e e') = 
    case mergeEmpty pfM of {Dict -> do
      Just (VPair v1 v2) <- fmap (fromLVal proxy) $ eval' e
      eval' $ subst pfA1 (valToExp v1) $ subst pfA2 (valToExp v2) e'
    }

  valToExpDomain _ (VPair v1 v2) = Pair MergeE (valToExp v1) (valToExp v2)

-- State Monad -------------------------------------------------

data LState' :: LType sig -> LType sig ~> LType sig
type instance Apply (LState' s) t = s ⊸ s ⊗ t

type LState s t = LState' s @@ t

-- Defunctionalization from singletons library!
class LFunctor lang (f :: LType sig ~> LType sig) where
  lfmap :: LExp lang 'Empty ((s ⊸ t) ⊸ f @@ s ⊸ f @@ t)
class LFunctor lang f => LApplicative lang f where
  lpure :: LExp lang 'Empty (t ⊸ f @@ t)
  llift :: LExp lang 'Empty (f @@ (s ⊸ t) ⊸ f @@ s ⊸ f @@ t)
class LApplicative lang m => LMonad lang m where
  lbind :: LExp lang 'Empty (m @@ s ⊸ (s ⊸ m @@ t) ⊸ m @@ t)

instance Domain TensorDom lang => LFunctor lang (LState' s) where
  lfmap = λ $ \f -> λ $ \fs -> λ $ \r ->
    var fs `app` var r `letPair` \(r,s) ->
    var r ⊗ (var f `app` var s)

instance Domain TensorDom lang => LApplicative lang (LState' r) where
  lpure = λ $ \s -> λ $ \r -> var r ⊗ var s

  -- this function is hard to write because of the limits of Haskell's type
  -- inference for contexts. As a result, we have to give annotations with the
  -- intermediate contexts with the precise variables generated by Fresh and
  -- Fresh2 in λ and letPair. It would be sufficient to only give the
  -- annotations for foo', but we also include foo to see how the reasoning
  -- works.
  llift :: forall s t. 
           LExp lang 'Empty (LState r (s ⊸ t) ⊸ LState r s ⊸ LState r t)
  llift = λ $ \ff -> λ $ \fs -> λ $ \r -> foo ff fs r
    where
      foo :: ( x1 ~ 'Z, x2 ~ 'S 'Z, x3 ~ 'S ('S 'Z)
             , g ~ 'N ('Cons ('Used (LState r (s ⊸ t))) g')
             , g' ~ 'Cons ('Used (LState r s)) ('End r))
          => Var x1 (LState r (s ⊸ t))
          -> Var x2 (LState r s)
          -> Var x3 r
          -> LExp lang g (r ⊗ t)
      foo ff fs r = var ff `app` var r `letPair` foo' fs

      foo' :: ( z ~ 'S 'Z, x ~ 'S ('S ('S 'Z)), y ~ 'S ('S ('S ('S 'Z)))
              , g ~ 'N ('Cons 'Unused ('Cons ('Used (LState r s)) ('Cons 'Unused g')))
              , g' ~ 'Cons ('Used r) ('End (s ⊸ t)) )
           => Var z (LState r s)
           -> (Var x r, Var y s)
           -> LExp lang g (r ⊗ t)
      foo' fs (r,f) = var fs `app` var r `letPair` \ (r,s) ->
        var r ⊗ (var f `app` var s)

--    var ff `app` var r `letPair` \ (r,f) -> foo fs f r
--    var fs `app` var r `letPair` \ (r,s) ->
--    var r ⊗ (var f `app` var s)

instance Domain TensorDom lang => LMonad lang (LState' s) where
  lbind = λ $ \ ms -> λ $ \ f -> λ $ \r -> 
     var ms `app` var r `letPair` \(r,s) -> 
     var f `app` var s `app` var r

-- Linearity monad transformer
data LinT lang (m :: LType sig ~> LType sig) :: * -> * where
  LinT :: Lift lang (m @@ Lower a) -> LinT lang m a

forceT :: LinT lang m a -> LExp lang 'Empty (m @@ Lower a)
forceT (LinT e) = force e
suspendT :: LExp lang 'Empty (m @@ Lower a) -> LinT lang m a
suspendT = LinT . Suspend

lowerT :: Domain LowerDom lang
       => LExp lang 'Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
lowerT = λ $ \g -> λ $ \ x -> 
          var g >! \f ->
          var x >! \a -> put $ f a

instance (Domain LowerDom lang, LFunctor lang f) 
      => Functor (LinT lang f) where
  fmap (g :: a -> b) (x :: LinT lang f a) = 
    suspendT $ lfmap @lang @f `app` (lowerT `app` put g) `app` forceT x
instance (Domain LowerDom lang, LApplicative lang f) 
      => Applicative (LinT lang f) where
  pure a = suspendT $ lpure @lang @f `app` put a

  (<*>) :: forall a b. LinT lang f (a -> b) -> LinT lang f a -> LinT lang f b
  g <*> a = suspendT $ foo `app` forceT a
    where
      g' :: LExp lang 'Empty (f @@ (Lower a ⊸ Lower b))
      g' = lfmap @lang @f @(Lower (a -> b)) @(Lower a ⊸ Lower b) 
            `app` lowerT `app` forceT g
      foo :: LExp lang 'Empty (f @@ (Lower a) ⊸ f @@ (Lower b))
      foo = llift @lang @f @(Lower a) @(Lower b) `app` g'

instance (Domain LowerDom lang, LMonad lang m)
      => Monad (LinT lang m) where
  (>>=) :: forall a b. LinT lang m a -> (a -> LinT lang m b) -> LinT lang m b
  x >>= f = suspendT mb
    where
      f' :: LExp lang 'Empty (Lower a ⊸ m @@ (Lower b))
      f' = λ $ \ x -> var x >! (forceT . f)
      mb :: LExp lang 'Empty (m @@ Lower b)
      mb = lbind @lang @m @(Lower a) @(Lower b) `app` forceT x `app` f'   

-- Lower -------------------------------------------------------

data LowerSig ty where
  LowerSig :: * -> LowerSig ty
type Lower a = ('Sig (InSig LowerSig sig) ('LowerSig a) :: LType sig)

data LowerExp :: forall sig. ExpDom sig where
  Put :: a -> LowerExp exp 'Empty (Lower a)
  LetBang :: Merge g1 g2 g
          -> exp g1 (Lower a)
          -> (a -> exp g2 t)
          -> LowerExp exp g t
data LowerVal :: forall sig. ValDom sig where
  VPut :: a -> LowerVal val (Lower a)

type LowerDom = '(LowerExp, LowerVal)

proxyLower :: Proxy LowerDom
proxyLower = Proxy

put :: Domain LowerDom lang
    => a -> LExp lang 'Empty (Lower a)
put a = Dom proxyLower $ Put a

(>!) :: (Domain LowerDom lang, CMerge g1 g2 g)
     => LExp lang g1 (Lower a)
     -> (a -> LExp lang g2 t)
     -> LExp lang g t
e >! f = Dom proxyLower $ LetBang merge e f

vput :: Domain LowerDom lang
     => a -> LVal lang (Lower a)
vput a = VDom proxyLower $ VPut a

instance Domain LowerDom lang
      => Language LowerDom lang where
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


-- Additive Sums

data PlusSig ty = PlusSig ty ty
type (⊕) (s :: LType sig) (t :: LType sig) =
    'Sig (InSig PlusSig sig) ('PlusSig s t)


data PlusExp :: forall sig. ExpDom sig where
  Inl  :: forall t2 t1 exp g. exp g t1 -> PlusExp exp g (t1 ⊕ t2)
  Inr  :: exp g t2 -> PlusExp exp g (t1 ⊕ t2)
  Case :: Merge g1 g2 g
       -> AddCtx x1 s1 g2 g21
       -> AddCtx x2 s2 g2 g22
       -> exp g1 (s1 ⊕ s2)
       -> exp g21 t
       -> exp g22 t
       -> PlusExp exp g t

data PlusVal :: forall sig. ValDom sig where
  VInl :: val t1 -> PlusVal val (t1 ⊕ t2)
  VInr :: val t2 -> PlusVal val (t1 ⊕ t2)

type PlusDom = '(PlusExp, PlusVal)

proxyPlus :: Proxy PlusDom
proxyPlus = Proxy

inl :: Domain PlusDom lang
    => LExp lang g t1 -> LExp lang g (t1 ⊕ t2)
inl e = Dom proxyPlus $ Inl e

inr :: Domain PlusDom lang
    => LExp lang g t2 -> LExp lang g (t1 ⊕ t2)
inr e = Dom proxyPlus $ Inr e

caseof :: forall sig lang s1 s2 g g1 g2 g21 g22 t.
          (Domain PlusDom lang,
           CAddCtx (Fresh g) s1 g2 g21,
           CAddCtx (Fresh g) s2 g2 g22,
           CMerge g1 g2 g)
       => LExp lang g1 (s1 ⊕ s2)
       -> (Var (Fresh g) s1 -> LExp lang g21 t)
       -> (Var (Fresh g) s2 -> LExp lang g22 t)
       -> LExp lang g t
caseof e f1 f2 = Dom proxyPlus $ Case merge pfA1 pfA2 e (f1 v1) (f2 v2)
  where
    pfA1 :: AddCtx (Fresh g) s1 g2 g21
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh g) s2 g2 g22
    pfA2 = addCtx
    v1 :: Var (Fresh g) s1
    v1 = addToSIdent pfA1
    v2 :: Var (Fresh g) s2
    v2 = addToSIdent pfA2

instance Domain PlusDom lang
      => Language PlusDom lang where

  substDomain _ pfA s (Inl e) = inl $ subst pfA s e
  substDomain _ pfA s (Inr e) = inr $ subst pfA s e
  substDomain _ pfA s (Case pfM pfA1 pfA2 e e1 e2) =
    case mergeAddSplit pfM pfA of
      Left  (pfA1',pfM1) -> 
        Dom proxyPlus $ Case pfM1 pfA1 pfA2 (subst pfA1' s e) e1 e2
      Right (pfA2',pfM2) -> undefined -- TODO

  evalDomain _     (Inl e) = fmap (VDom proxyPlus . VInl) $ eval' e
  evalDomain _     (Inr e) = fmap (VDom proxyPlus . VInr) $ eval' e
  evalDomain proxy (Case pfM pfA1 pfA2 e e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      v <- eval' e
      case fromLVal proxy v of
        Just (VInl v1) -> eval' $ subst pfA1 (valToExp v1) e1
        Just (VInr v2) -> eval' $ subst pfA2 (valToExp v2) e2
    }   

  valToExpDomain _ (VInl v) = Inl $ valToExp v
  valToExpDomain _ (VInr v) = Inr $ valToExp v


-- Additive Product

data WithSig ty = WithSig ty ty
type (&) (s :: LType sig) (t :: LType sig) = 
    'Sig (InSig WithSig sig) ('WithSig s t)

data WithExp :: forall sig. ExpDom sig where
  With  :: exp g t1 -> exp g t2 -> WithExp exp g (t1 & t2)
  Proj1 :: exp g (t1 & t2) -> WithExp exp g t1
  Proj2 :: exp g (t1 & t2) -> WithExp exp g t2
data WithVal :: forall sig. ValDom sig where
  VWith :: val t1 -> val t2 -> WithVal val (t1 & t2)

type WithDom = '(WithExp, WithVal)

proxyWith :: Proxy WithDom
proxyWith = Proxy

(&) :: Domain WithDom lang
    => LExp lang g t1 -> LExp lang g t2 -> LExp lang g (t1 & t2)
e1 & e2 = Dom proxyWith $ With e1 e2

proj1 :: Domain WithDom lang
      => LExp lang g (t1 & t2) -> LExp lang g t1
proj1 = Dom proxyWith . Proj1

proj2 :: Domain WithDom lang
      => LExp lang g (t1 & t2) -> LExp lang g t2
proj2 = Dom proxyWith . Proj2

instance Domain WithDom lang => Language WithDom lang where
  substDomain _ pfA s (With e1 e2) = subst pfA s e1 & subst pfA s e2
  substDomain _ pfA s (Proj1 e)    = proj1 $ subst pfA s e
  substDomain _ pfA s (Proj2 e)    = proj2 $ subst pfA s e


  -- TODO: Think about laziness and evaluation order
  evalDomain _ (With e1 e2) = do
    v1 <- eval' e1 
    v2 <- eval' e2
    return $ VDom proxyWith $ VWith v1 v2
  evalDomain _ (Proj1 e) = do
    Just (VWith v1 v2) <- fmap (fromLVal proxyWith) $ eval' e
    return v1
  evalDomain _ (Proj2 e) = do
    Just (VWith v1 v2) <- fmap (fromLVal proxyWith) $ eval' e
    return v2

  valToExpDomain _ (VWith v1 v2) = With (valToExp v1) (valToExp v2)


-- concrete examples

type MultiplicativeProductSig m = '(m,'[ OneSig, TensorSig ])
type MultiplicativeProductDom m = ( '[ OneDom, TensorDom ] 
    :: Lang (MultiplicativeProductSig m) )

swapMP :: Monad m => Lift (MultiplicativeProductDom m) (s ⊗ t ⊸ t ⊗ s)
swapMP = Suspend . λ $ \ pr ->
    var pr `letPair` \(x,y) ->
    var y ⊗ var x


--type MELL


{-


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
