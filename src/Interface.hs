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

import Prelim
import Types
import Context
import Proofs
import Classes
import Lang

type Var x s = SNat x

var :: Var x s -> LExp sig (Singleton x s) s
var x = Var $ singSing x

-- Implication ----------------------------------

data LolliSig ty where
  LolliSig :: ty -> ty -> LolliSig ty

type (⊸) (s :: LType sig) (t :: LType sig) =
  'Sig (InSig LolliSig sig) ('LolliSig s t)
infixr 0 ⊸

data LolliExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Abs :: AddCtx x s g g'
      -> LExp lang g' t
      -> LolliExp lang g (s ⊸ t)
  App :: Merge g1 g2 g
      -> LExp lang g1 (s ⊸ t)
      -> LExp lang g2 s
      -> LolliExp lang g t
data LolliVal :: Lang sig -> LType sig -> * where
  VAbs :: AddCtx x s 'Empty g'
       -> LExp lang g' t
       -> LolliVal lang (s ⊸ t)

type LolliDom = '(LolliExp, LolliVal)
proxyLolli :: Proxy LolliDom
proxyLolli = Proxy

λ :: forall lang s t g g'. 
     (Domain LolliDom lang, CAddCtx (Fresh g) s g g')
  => (Var (Fresh g) s -> LExp lang g' t)
  -> LExp lang g (s ⊸ t)
λ f = Dom proxyLolli $ Abs pfA (f x) where
  pfA :: AddCtx (Fresh g) s g g'
  pfA  = addCtx
  x   :: SNat (Fresh g)
  x    = addToSNat pfA

app :: (Domain LolliDom lang, CMerge g1 g2 g3)
    => LExp lang g1 (s ⊸ t)
    -> LExp lang g2 s
    -> LExp lang g3 t
e1 `app` e2 = Dom proxyLolli $ App merge e1 e2


letin :: forall lang s t g g1 g2 g2'.
         (Domain LolliDom lang, CAddCtx (Fresh g2) s g2 g2', CMerge g1 g2 g)
      => LExp lang g1 s
      -> (Var (Fresh g2) s -> LExp lang g2' t)
      -> LExp lang g t
letin e f = λ f `app` e

substAbs :: forall lang x s y t g g' g'' r.
            Domain LolliDom lang
         => AddCtx x s g g'
         -> LExp lang Empty s
         -> AddCtx y t g' g''
         -> LExp lang g'' r
         -> LExp lang g (t ⊸ r)
substAbs pfA s pfA' e = Dom proxyLolli $ Abs pfA0 $ subst pfA0' s e
  where
    pfI :: In x s g'
    pfI = addIn pfA
    pfI' :: In x s g''
    pfI' = inAdd pfI pfA'
    pfEq :: Dict (g ~ Remove x g')
    pfEq = addRemoveEquiv pfA
    pfA0 :: AddCtx y t g (Remove x g'')
    pfA0 = case pfEq of Dict -> inAddRemoveLater pfI pfA' 
    pfA0' :: AddCtx x s (Remove x g'') g''
    pfA0' = inAddRemove pfI'

instance Domain LolliDom lang => Language LolliDom lang where
  substDomain pfA s (Abs pfA' e)   = substAbs pfA s pfA' e
  substDomain pfA s (App pfM e1 e2)= 
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxyLolli $ App pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxyLolli $ App pfM2 e1 (subst pfA2 s e2)

  evalDomain (Abs pfA e) = return $ VDom proxyLolli $ VAbs pfA e
  evalDomain (App pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
    VAbs pfA e1' <- evalToValDom proxyLolli e1
    e2'          <- eval e2
    case addRemoveEquiv pfA of {Dict -> 
    eval' $ subst pfA e2' e1'
  }}

  valToExpDomain (VAbs pfA e) = Abs pfA e


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

data OneExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Unit :: OneExp lang 'Empty One
  LetUnit :: Merge g1 g2 g -> LExp lang g1 One -> LExp lang g2 t -> OneExp lang g t

data OneVal :: forall sig. Lang sig -> LType sig -> * where
  VUnit :: OneVal lang One

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
  substDomain pfA s (LetUnit pfM e1 e2) = 
    case mergeAddSplit pfM pfA of 
      Left  (pfA1,pfM1) -> Dom proxyOne $ LetUnit pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxyOne $ LetUnit pfM2 e1 (subst pfA2 s e2)

  evalDomain Unit = return vunit
  evalDomain (LetUnit pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      VUnit <- evalToValDom proxyOne e1
      eval' e2
    }

  valToExpDomain VUnit = Unit


-- Tensor ------------------------------------------------------


data TensorSig ty = TensorSig ty ty

type (⊗) (s :: LType sig) (t :: LType sig) = 
     'Sig (InSig TensorSig sig) ('TensorSig s t)

data TensorExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Pair :: Merge g1 g2 g
       -> LExp lang g1 t1 -> LExp lang g2 t2 -> TensorExp lang g (t1 ⊗ t2)
  LetPair :: Merge g1 g2'' g -> AddCtx x1 s1 g2'' g2' -> AddCtx x2 s2 g2' g2
          -> LExp lang g1 (s1 ⊗ s2) -> LExp lang g2 t -> TensorExp lang g t
data TensorVal :: Lang sig -> LType sig -> * where
  VPair :: LVal lang t1 -> LVal lang t2 -> TensorVal lang (t1 ⊗ t2)

type TensorDom  = '(TensorExp, TensorVal)

proxyTensor :: Proxy TensorDom
proxyTensor = Proxy

(⊗) :: (Domain TensorDom lang, CMerge g1 g2 g)
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

substLetPair :: forall lang x s g g' g1 g2 g2' g2'' x1 x2 s1 s2 t.
                Domain TensorDom lang
             => AddCtx x s g g'
             -> LExp lang Empty s
             -> Merge g1 g2'' g' 
             -> AddCtx x1 s1 g2'' g2' 
             -> AddCtx x2 s2 g2' g2
             -> LExp lang g1 (s1 ⊗ s2) 
             -> LExp lang g2 t
             -> LExp lang g t
substLetPair pfA s pfM pfA1 pfA2 e e' = 
  case addRemoveEquiv pfA of {Dict ->
  case mergeAddSplit pfM pfA of
    Left  ( pfA1' :: AddCtx x s (Remove x g1) g1
          , pfM1  :: Merge (Remove x g1) g2'' g) -> 
      Dom proxyTensor $ LetPair pfM1 pfA1 pfA2 (subst pfA1' s e) e'
    Right ( pfA2' :: AddCtx x s (Remove x g2'') g2''
          , pfM2  :: Merge g1 (Remove x g2'') g) -> 
      Dom proxyTensor $ LetPair pfM2 pfA10 pfA20 e $ subst pfA0 s e'
      where
        pfI2'' :: In x s g2''
        pfI2'' = addIn pfA2'
        pfI2' :: In x s g2'
        pfI2' = inAdd pfI2'' pfA1
        pfI2 :: In x s g2
        pfI2 = inAdd pfI2' pfA2
        pfA0 :: AddCtx x s (Remove x g2) g2
        pfA0 = inAddRemove pfI2
        pfA10 :: AddCtx x1 s1 (Remove x g2'') (Remove x g2')
        pfA10 = inAddRemoveLater pfI2'' pfA1
        pfA20 :: AddCtx x2 s2 (Remove x g2') (Remove x g2)
        pfA20 = inAddRemoveLater pfI2' pfA2
  }

instance Domain TensorDom lang
      => Language TensorDom lang where
  substDomain pfA s (Pair pfM e1 e2) = 
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxyTensor $ Pair pfM1 (subst pfA1 s e1) e2
      Right (pfA2,pfM2) -> Dom proxyTensor $ Pair pfM2 e1 (subst pfA2 s e2)
  substDomain pfA s (LetPair pfM pfA1 pfA2 e e') = 
    substLetPair pfA s pfM pfA1 pfA2 e e'

  evalDomain (Pair pfM e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      v1 <- eval' e1
      v2 <- eval' e2
      return $ vpair v1 v2
    }
  evalDomain (LetPair pfM pfA1 pfA2 e e') = 
    case mergeEmpty pfM of {Dict -> do
      VPair v1 v2 <- evalToValDom proxyTensor e
      eval' $ subst pfA1 (valToExp v1) $ subst pfA2 (valToExp v2) e'
    }

  valToExpDomain (VPair v1 v2) = Pair MergeE (valToExp v1) (valToExp v2)

-- Lower -------------------------------------------------------

data LowerSig ty where
  LowerSig :: * -> LowerSig ty
type Lower a = ('Sig (InSig LowerSig sig) ('LowerSig a) :: LType sig)

data LowerExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Put :: a -> LowerExp lang 'Empty (Lower a)
  LetBang :: Merge g1 g2 g
          -> LExp lang g1 (Lower a)
          -> (a -> LExp lang g2 t)
          -> LowerExp lang g t
data LowerVal :: Lang sig -> LType sig -> * where
  VPut :: a -> LowerVal lang (Lower a)

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
  substDomain pfA s (LetBang pfM e f) =
    case mergeAddSplit pfM pfA of
      Left  (pfA1,pfM1) -> Dom proxyLower $ LetBang pfM1 (subst pfA1 s e) f
      Right (pfA2,pfM2) -> Dom proxyLower $ LetBang pfM2 e f'
        where
          f' x = subst pfA2 s (f x)

  evalDomain (Put a) = return $ vput a
  evalDomain (LetBang pfM e f) = 
    case mergeEmpty pfM of {Dict -> do
      VPut a <- evalToValDom proxyLower e
      eval' $ f a
    }

  valToExpDomain (VPut a) = Put a

-- Additive Sums

data PlusSig ty = PlusSig ty ty
type (⊕) (s :: LType sig) (t :: LType sig) =
    'Sig (InSig PlusSig sig) ('PlusSig s t)


data PlusExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Inl  :: LExp lang g t1 -> PlusExp lang g (t1 ⊕ t2)
  Inr  :: LExp lang g t2 -> PlusExp lang g (t1 ⊕ t2)
  Case :: Merge g1 g2 g
       -> AddCtx x1 s1 g2 g21
       -> AddCtx x2 s2 g2 g22
       -> LExp lang g1 (s1 ⊕ s2)
       -> LExp lang g21 t
       -> LExp lang g22 t
       -> PlusExp lang g t

data PlusVal :: Lang sig -> LType sig -> * where
  VInl :: LVal lang t1 -> PlusVal lang (t1 ⊕ t2)
  VInr :: LVal lang t2 -> PlusVal lang (t1 ⊕ t2)

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
    v1 = addToSNat pfA1
    v2 :: Var (Fresh g) s2
    v2 = addToSNat pfA2


oplus :: (Domain LolliDom lang, Domain PlusDom lang, Domain WithDom lang)
    => LExp lang 'Empty ((s1 ⊸ t) & (s2 ⊸ t) ⊸ s1 ⊕ s2 ⊸ t)
oplus = λ $ \f -> λ $ \x -> 
  caseof (var x)
    (\x1 -> proj1 (var f) `app` var x1)
    (\x2 -> proj2 (var f) `app` var x2)

instance Domain PlusDom lang
      => Language PlusDom lang where

  substDomain pfA s (Inl e) = inl $ subst pfA s e
  substDomain pfA s (Inr e) = inr $ subst pfA s e
  substDomain pfA s (Case pfM pfA1 pfA2 e e1 e2) =
    case mergeAddSplit pfM pfA of
      Left  (pfA1',pfM1) -> 
        Dom proxyPlus $ Case pfM1 pfA1 pfA2 (subst pfA1' s e) e1 e2
      Right (pfA2',pfM2) -> undefined -- TODO

  evalDomain (Inl e) = VDom proxyPlus . VInl <$> eval' e
  evalDomain (Inr e) = VDom proxyPlus . VInr <$> eval' e
  evalDomain (Case pfM pfA1 pfA2 e e1 e2) = 
    case mergeEmpty pfM of {Dict -> do
      v <- eval' e
      case fromLVal proxyPlus v of
        Just (VInl v1) -> eval' $ subst pfA1 (valToExp v1) e1
        Just (VInr v2) -> eval' $ subst pfA2 (valToExp v2) e2
    }   

  valToExpDomain (VInl v) = Inl $ valToExp v
  valToExpDomain (VInr v) = Inr $ valToExp v


-- Additive Product

data WithSig ty = WithSig ty ty
type (&) (s :: LType sig) (t :: LType sig) = 
    'Sig (InSig WithSig sig) ('WithSig s t)

data WithExp :: Lang sig -> Ctx sig -> LType sig -> * where
  With  :: LExp lang g t1 -> LExp lang g t2 -> WithExp lang g (t1 & t2)
  Proj1 :: LExp lang g (t1 & t2) -> WithExp lang g t1
  Proj2 :: LExp lang g (t1 & t2) -> WithExp lang g t2
data WithVal :: Lang sig -> LType sig -> * where -- Lazy values
  VWith :: LExp lang 'Empty t1 -> LExp lang 'Empty t2 -> WithVal lang (t1 & t2)

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
  substDomain pfA s (With e1 e2) = subst pfA s e1 & subst pfA s e2
  substDomain pfA s (Proj1 e)    = proj1 $ subst pfA s e
  substDomain pfA s (Proj2 e)    = proj2 $ subst pfA s e


  -- TODO: Think about laziness and evaluation order
  evalDomain (With e1 e2) = return $ VDom proxyWith $ VWith e1 e2
  evalDomain (Proj1 e) = do
    VWith e1 e2 <- evalToValDom proxyWith e
    eval' e1
  evalDomain (Proj2 e) = do
    VWith e1 e2 <- evalToValDom proxyWith e
    eval' e2

  valToExpDomain (VWith e1 e2) = With e1 e2



-- State Monad -------------------------------------------------

data LState' :: LType sig -> LType sig ~> LType sig
type instance Apply (LState' s) t = s ⊸ s ⊗ t

type LState s t = LState' s @@ t
class (Domain TensorDom lang, Domain LowerDom lang, Domain OneDom lang, Domain LolliDom lang) 
   => HasLStateDom lang
instance (Domain TensorDom lang, Domain LowerDom lang, Domain OneDom lang, Domain LolliDom lang) 
   => HasLStateDom lang

runLState :: HasLStateDom lang
          => LinT lang (LState' s) a -> Lift lang s -> Lift lang (s ⊗ Lower a)
runLState st s = Suspend $ forceT st `app` force s

execLState :: HasLStateDom lang 
           => LinT lang (LState' s) a -> Lift lang s -> Lift lang s
execLState st s = Suspend $ 
    forceT st `app` force s `letPair` \(s',a) ->
    var a >! \_ ->
    var s'

evalLState :: HasLStateDom lang
           => LinT lang (LState' s) a
           -> Lift lang s
           -> Lift lang (s ⊸ One) -- a way to eliminate the state
           -> Lin lang a
evalLState st s f = suspendL $
    force (runLState st s) `letPair` \(s',a) ->
    force f `app` var s' `letUnit` var a

-- Defunctionalization from singletons library!
class LFunctor lang (f :: LType sig ~> LType sig) where
  lfmap :: LExp lang 'Empty ((s ⊸ t) ⊸ f @@ s ⊸ f @@ t)
class LFunctor lang f => LApplicative lang f where
  lpure :: LExp lang 'Empty (t ⊸ f @@ t)
  llift :: LExp lang 'Empty (f @@ (s ⊸ t) ⊸ f @@ s ⊸ f @@ t)
class LApplicative lang m => LMonad lang m where
  lbind :: LExp lang 'Empty (m @@ s ⊸ (s ⊸ m @@ t) ⊸ m @@ t)

instance HasLStateDom lang => LFunctor lang (LState' s) where
  lfmap = λ $ \f -> λ $ \fs -> λ $ \r ->
    var fs `app` var r `letPair` \(r,s) ->
    var r ⊗ (var f `app` var s)

instance HasLStateDom lang => LApplicative lang (LState' r) where
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
--    var ff `app` var r `letPair` \ (r,f) -> foo fs f r
--    var fs `app` var r `letPair` \ (r,s) ->
--    var r ⊗ (var f `app` var s)

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


instance HasLStateDom lang => LMonad lang (LState' s) where
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

lowerT :: (Domain LolliDom lang, Domain LowerDom lang)
       => LExp lang 'Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
lowerT = λ $ \g -> λ $ \ x -> 
          var g >! \f ->
          var x >! \a -> put $ f a

instance (Domain LowerDom lang, Domain LolliDom lang, LFunctor lang f) 
      => Functor (LinT lang f) where
  fmap (g :: a -> b) (x :: LinT lang f a) = 
    suspendT $ lfmap @lang @f `app` (lowerT `app` put g) `app` forceT x
instance (Domain LowerDom lang, Domain LolliDom lang, LApplicative lang f) 
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

instance (Domain LowerDom lang, Domain LolliDom lang, LMonad lang m)
      => Monad (LinT lang m) where
  (>>=) :: forall a b. LinT lang m a -> (a -> LinT lang m b) -> LinT lang m b
  x >>= f = suspendT mb
    where
      f' :: LExp lang 'Empty (Lower a ⊸ m @@ (Lower b))
      f' = λ $ \ x -> var x >! (forceT . f)
      mb :: LExp lang 'Empty (m @@ Lower b)
      mb = lbind @lang @m @(Lower a) @(Lower b) `app` forceT x `app` f'   






-- concrete examples

type MultiplicativeProductSig m = '(m,'[ OneSig, TensorSig, LolliSig ])
type MultiplicativeProductDom m = ('Lang '[ OneDom, TensorDom, LolliDom ] 
    :: Lang (MultiplicativeProductSig m) )

swapMP :: Monad m => Lift (MultiplicativeProductDom m) (s ⊗ t ⊸ t ⊗ s)
swapMP = Suspend . λ $ \ pr ->
    var pr `letPair` \(x,y) ->
    var y ⊗ var x




-- Linearity Monad and Comonad -------------------------------

type family Bang (lang :: Lang sig) (a :: LType sig) :: LType sig where
  Bang lang a = Lower (Lift lang a)
data Lin lang a where
  Lin :: Lift lang (Lower a) -> Lin lang a



instance Domain LowerDom lang => Functor (Lin lang) where
  -- f :: a -> b
  -- a :: Lin a ~ Lift f (Lower a)
  -- fmap f a :: Lift (Lower b)
  fmap f (Lin (Suspend e)) = Lin . Suspend $ e >! \ x → put (f x)
instance  Domain LowerDom lang => Applicative (Lin lang) where
  pure a = Lin $ Suspend (put a)
  -- a :: Lift (Lower a) 
  -- f :: Lift (Lower (a -> b))
  -- f <*> a :: Lift (Lower b)
  Lin (Suspend f) <*> Lin (Suspend e) = Lin . Suspend $ e >! \ x -> 
                                                        f >! \ f' -> 
                                                        put (f' x)
instance  Domain LowerDom lang => Monad (Lin lang) where
  -- e :: Lin a = Lift (Lower a)
  -- f :: a -> Lift (Lower b)
  Lin (Suspend e) >>= f  = Lin . Suspend $ e >! \ x -> forceL (f x)



forceL :: Lin lang a -> LExp lang 'Empty (Lower a)
forceL (Lin e) = force e

suspendL :: LExp lang 'Empty (Lower a) -> Lin lang a
suspendL = Lin . Suspend 

-- evalL :: forall sig (lang :: Lang sig) a.
--          Monad (SigEffect sig) => Lin lang a -> SigEffect sig (Lin lang a)
-- evalL (Lin e) = Lin <$> evalL' e where
--   evalL' :: forall sig (lang :: Lang sig) a. Monad (SigEffect sig) 
--          => Lift lang (Lower a) -> SigEffect sig (Lift lang (Lower a))
--   evalL' (Suspend e) = Suspend <$> eval e

evalVal :: forall sig (lang :: Lang sig) a. Monad (SigEffect sig) 
        => Lin lang a -> SigEffect sig (LVal lang (Lower a))
evalVal (Lin (Suspend e)) = eval' e

run :: forall sig (lang :: Lang sig) a. 
       (Monad (SigEffect sig), Domain LowerDom lang)
    => Lin lang a -> SigEffect sig a
run e = do
  Just (VPut a) <- fromLVal proxyLower <$> evalVal e
  return a

-- Monads in the linear fragment ----------------------------------
{-
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
