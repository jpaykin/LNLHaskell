{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase, RankNTypes, TypeFamilyDependencies,
             ConstraintKinds
#-}
{-# OPTIONS_GHC -Wall -Wcompat #-}

module Interface where

import Data.Kind
import Data.Proxy
import Data.Singletons

import Types
import Context
import Proofs
import Classes
import Lang

var :: forall x s g lang. CSingletonCtx x s g
    => LExp lang g s
var = Var $ singletonCtx @x

-- Implication ----------------------------------

data LolliSig sig where
  LolliSig :: LType sig -> LType sig -> LolliSig ty

type (⊸) (s :: LType sig) (t :: LType sig) =
  ('LType (InSig LolliSig sig) ('LolliSig s t) :: LType sig)
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
  -- The value is a closure
  VAbs :: ECtx lang g
       -> AddCtx x s g g'
       -> LExp lang g' t
       -> LolliVal lang (s ⊸ t)

type LolliDom = '(LolliExp, LolliVal)
proxyLolli :: Proxy LolliDom
proxyLolli = Proxy

instance Show (LolliExp lang g t) where
  show (Abs pfA e) = "λ " ++ show (addToSNat pfA) ++ " . " ++ show e
  show (App _ e1 e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"

λ :: forall lang x s t g g' g''. 
     ( Domain LolliDom lang
     , CAddCtx x s g g'
     , CSingletonCtx x s g'' 
     , x ~ Fresh g)
  => (LExp lang g'' s -> LExp lang g' t) -> LExp lang g (s ⊸ t)
λ f = Dom proxyLolli $ Abs (addCtx @x) (f . Var $ singletonCtx @x) 

app :: (Domain LolliDom lang, CMerge g1 g2 g3)
    => LExp lang g1 (s ⊸ t)
    -> LExp lang g2 s
    -> LExp lang g3 t
e1 `app` e2 = Dom proxyLolli $ App merge e1 e2


letin :: forall lang x s t g g1 g2 g2' g2''.
         ( Domain LolliDom lang
         , CAddCtx x s g2 g2'
         , CSingletonCtx x s g2''
         , CMerge g1 g2 g
         , x ~ Fresh g2)
      => LExp lang g1 s
      -> (LExp lang g2'' s -> LExp lang g2' t)
      -> LExp lang g t
letin e f = λ f `app` e

-- Sanity check examples 

ex :: Domain LolliDom lang => LExp lang 'Empty ((s ⊸ t) ⊸ s ⊸ t)
ex = λ $ \x -> λ $ \y -> x `app` y

--ex2 :: Domain LolliDom lang => LExp lang 'Empty (s ⊸ t ⊸ s)
--ex2 = λ $ \x -> λ $ \y -> x

--ex3 :: (Domain LolliDom lang, Domain TensorDom lang) => LExp lang 'Empty (σ ⊸ σ ⊗ σ)
--ex3 = λ $ \x -> x ⊗ x

-- apply an expression to a value
-- this is conbined with evaluation
evalApplyValue :: forall sig (lang :: Lang sig) g s t.
                  Domain LolliDom lang
               => ECtx lang g -> LExp lang g (s ⊸ t) -> LVal lang s 
               -> SigEffect sig (LVal lang t)
evalApplyValue ρ e v = eval' ρ' $ Dom proxyLolli $ App pfM e $ Var pfS
  where
    pfS :: SingletonCtx (Fresh g) s (Singleton (Fresh g) s)
    pfS = singSing $ knownFresh ρ 

    ρ' :: ECtx lang (Add (Fresh g) s g)
    ρ' = addFreshSCtx ρ (ValData v)

    pfM :: Merge g (Singleton (Fresh g) s) (Add (Fresh g) s g)
    pfM = mergeAddFresh @s ρ


-- Can we make this CBN instead of CBV? Can we have both?
instance WFDomain LolliDom lang => Domain LolliDom lang where
  evalDomain ρ (Abs pfA e) = return $ VDom proxyLolli $ VAbs ρ pfA e
  evalDomain ρ (App pfM e1 e2) = do
      VAbs ρ' pfA e1' <- evalToValDom proxyLolli ρ1 e1
      v2              <- eval' ρ2 e2
      eval' (addSCtx pfA ρ' $ ValData v2) e1'
    where
      (ρ1,ρ2) = splitSCtx pfM ρ


-- DEFINING DOMAINS ---------------------------------

-- One ---------------------------------------

data OneSig sig where
  OneSig :: OneSig sig

type One = ('LType (InSig OneSig sig) 'OneSig :: LType sig)

data OneExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Unit :: OneExp lang 'Empty One
  LetUnit :: Merge g1 g2 g -> LExp lang g1 One -> LExp lang g2 t -> OneExp lang g t

data OneVal :: forall sig. Lang sig -> LType sig -> * where
  VUnit :: OneVal lang One

type OneDom = '(OneExp,OneVal)

proxyOne :: Proxy OneDom
proxyOne = Proxy

instance Show (OneExp lang g t) where
  show Unit = "()"
  show (LetUnit _ e1 e2) = "let () = " ++ show e1 ++ " in " ++ show e2

unit :: Domain OneDom lang
     => LExp lang 'Empty One
unit = Dom proxyOne Unit

letUnit :: (Domain OneDom lang, CMerge g1 g2 g)
        => LExp lang g1 One -> LExp lang g2 t -> LExp lang g t
e1 `letUnit` e2 = Dom proxyOne $ LetUnit merge e1 e2

vunit :: Domain OneDom lang
      => LVal lang One
vunit = VDom proxyOne VUnit

instance WFDomain OneDom lang
      => Domain OneDom lang where

  evalDomain _ Unit = return vunit
  evalDomain ρ (LetUnit pfM e1 e2) = do
    VUnit <- evalToValDom proxyOne ρ1 e1
    eval' ρ2 e2
    where
      (ρ1,ρ2) = splitSCtx pfM ρ



-- Tensor ------------------------------------------------------


data TensorSig sig = TensorSig (LType sig) (LType sig)

type (⊗) (s :: LType sig) (t :: LType sig) = 
     'LType (InSig TensorSig sig) ('TensorSig s t)

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

instance Show (TensorExp lang g t) where
  show (Pair _ e1 e2) = "(" ++ show e1 ++ ", " ++ show e2 ++ ")"
  show (LetPair _ pfA1 pfA2 e e') = "let (" ++ show (addToSNat pfA1) ++ ", " ++ show (addToSNat pfA2)
    ++ ") = " ++ show e ++ " in " ++ show e'

(⊗) :: (Domain TensorDom lang, CMerge g1 g2 g)
     => LExp lang g1 s1 -> LExp lang g2 s2 -> LExp lang g (s1 ⊗ s2)
e1 ⊗ e2 = Dom proxyTensor $ Pair merge e1 e2

letPair :: forall sig (lang :: Lang sig) x1 x2 g g1 g2 g2' g2'' g21 g22 s1 s2 t.
         ( Domain TensorDom lang
         , CAddCtx x1 s1 g2'' g2'
         , CAddCtx x2 s2 g2' g2
         , CMerge g1 g2'' g
         , CSingletonCtx x1 s1 g21
         , CSingletonCtx x2 s2 g22
         , x1 ~ Fresh g
         , x2 ~ Fresh2 g
         )
        => LExp lang g1 (s1 ⊗ s2)
        -> ((LExp lang g21 s1, LExp lang g22 s2) -> LExp lang g2 t)
        -> LExp lang g t
letPair e f = Dom proxyTensor $ LetPair merge pfA1 pfA2 e e'
  where
    pfA1 :: AddCtx (Fresh g) s1 g2'' g2'
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh2 g) s2 g2' g2
    pfA2 = addCtx

    e' :: LExp lang g2 t
    e' = f (Var $ singletonCtx @x1, Var $ singletonCtx @x2)

vpair :: Domain TensorDom lang
      => LVal lang s1 -> LVal lang s2 -> LVal lang (s1 ⊗ s2)
vpair v1 v2 = VDom proxyTensor $ VPair v1 v2


instance WFDomain TensorDom lang
      => Domain TensorDom lang where

  evalDomain ρ (Pair pfM e1 e2) = do
      v1 <- eval' ρ1 e1
      v2 <- eval' ρ2 e2
      return $ vpair v1 v2
    where
      (ρ1,ρ2) = splitSCtx pfM ρ
  evalDomain ρ (LetPair pfM pfA pfA' e e') = do
      VPair v1 v2 <- evalToValDom proxyTensor ρ1 e
      eval' (ρ' v1 v2) e'
    where
      (ρ1,ρ2) = splitSCtx pfM ρ 
      ρ' v1 v2 = addSCtx pfA' (addSCtx pfA ρ2 (ValData v1)) (ValData v2)


-- Lift --------------------------------------------------------

data Lift (lang :: Lang sig) :: LType sig -> * where
  Suspend :: LExp lang 'Empty t -> Lift lang t

force :: Lift lang t -> LExp lang 'Empty t
force (Suspend e) = e

-- Lower -------------------------------------------------------

data LowerSig sig where
  LowerSig :: * -> LowerSig sig
type Lower a = ('LType (InSig LowerSig sig) ('LowerSig a) :: LType sig)

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

instance Show (LowerExp lang g t) where
  show (Put _) = "Put"
  show (LetBang _ e _) = show e ++ ">! ??"

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

instance WFDomain LowerDom lang
      => Domain LowerDom lang where

  evalDomain _ (Put a) = return $ vput a
  evalDomain ρ (LetBang pfM e f) = do
      VPut a <- evalToValDom proxyLower ρ1 e
      eval' ρ2 $ f a
    where
      (ρ1,ρ2) = splitSCtx pfM ρ



-- Additive Sums

data PlusSig sig = PlusSig (LType sig) (LType sig)
type (⊕) (s :: LType sig) (t :: LType sig) =
    'LType (InSig PlusSig sig) ('PlusSig s t)


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

instance Show (PlusExp lang g t) where
  show (Inl e) = "Inl " ++ show e
  show (Inr e) = "Inr " ++ show e
  show (Case _ _ _ _ _ _) = undefined

inl :: Domain PlusDom lang
    => LExp lang g t1 -> LExp lang g (t1 ⊕ t2)
inl e = Dom proxyPlus $ Inl e

inr :: Domain PlusDom lang
    => LExp lang g t2 -> LExp lang g (t1 ⊕ t2)
inr e = Dom proxyPlus $ Inr e

caseof :: forall lang x s1 s2 g g1 g2 g21 g22 g21' g22' t.
          ( Domain PlusDom lang
          , CAddCtx x s1 g2 g21, CSingletonCtx x s1 g21'
          , CAddCtx x s2 g2 g22, CSingletonCtx x s2 g22'
          , x ~ Fresh g
          , CMerge g1 g2 g)
       => LExp lang g1 (s1 ⊕ s2)
       -> (LExp lang g21' s1 -> LExp lang g21 t)
       -> (LExp lang g22' s2 -> LExp lang g22 t)
       -> LExp lang g t
caseof e f1 f2 = Dom proxyPlus $ 
    Case merge pfA1 pfA2 e (f1 . Var $ singletonCtx @x) (f2 . Var $ singletonCtx @x)
  where
    pfA1 :: AddCtx (Fresh g) s1 g2 g21
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh g) s2 g2 g22
    pfA2 = addCtx


instance WFDomain PlusDom lang
      => Domain PlusDom lang where

  evalDomain ρ (Inl e) = VDom proxyPlus . VInl <$> eval' ρ e
  evalDomain ρ (Inr e) = VDom proxyPlus . VInr <$> eval' ρ e
  evalDomain ρ (Case pfM pfA1 pfA2 e e1 e2) = do
      v <- evalToValDom proxyPlus ρ1 e
      case v of
        VInl v1 -> eval' (addSCtx pfA1 ρ2 (ValData v1)) e1
        VInr v2 -> eval' (addSCtx pfA2 ρ2 (ValData v2)) e2
    where
      (ρ1,ρ2) = splitSCtx pfM ρ



-- Additive Product

data WithSig sig = WithSig (LType sig) (LType sig)
type (&) (s :: LType sig) (t :: LType sig) = 
    'LType (InSig WithSig sig) ('WithSig s t)

data WithExp :: Lang sig -> Ctx sig -> LType sig -> * where
  With  :: LExp lang g t1 -> LExp lang g t2 -> WithExp lang g (t1 & t2)
  Proj1 :: LExp lang g (t1 & t2) -> WithExp lang g t1
  Proj2 :: LExp lang g (t1 & t2) -> WithExp lang g t2
data WithVal :: Lang sig -> LType sig -> * where -- Lazy values
  VWith :: ECtx lang g -> LExp lang g t1 -> LExp lang g t2 -> WithVal lang (t1 & t2)

type WithDom = '(WithExp, WithVal)

proxyWith :: Proxy WithDom
proxyWith = Proxy

instance Show (WithExp lang g t) where
  show = undefined

(&) :: Domain WithDom lang
    => LExp lang g t1 -> LExp lang g t2 -> LExp lang g (t1 & t2)
e1 & e2 = Dom proxyWith $ With e1 e2

proj1 :: Domain WithDom lang
      => LExp lang g (t1 & t2) -> LExp lang g t1
proj1 = Dom proxyWith . Proj1

proj2 :: Domain WithDom lang
      => LExp lang g (t1 & t2) -> LExp lang g t2
proj2 = Dom proxyWith . Proj2


oplus :: (Domain LolliDom lang, Domain PlusDom lang, Domain WithDom lang)
    => LExp lang 'Empty ((s1 ⊸ t) & (s2 ⊸ t) ⊸ s1 ⊕ s2 ⊸ t)
oplus = λ $ \f -> λ $ \x -> 
  caseof x
    (\x1 -> proj1 f `app` x1)
    (\x2 -> proj2 f `app` x2)

instance WFDomain WithDom lang => Domain WithDom lang where
  evalDomain ρ (With e1 e2) = return $ VDom proxyWith $ VWith ρ e1 e2
  evalDomain ρ (Proj1 e) = do
    VWith ρ' e1 _ <- evalToValDom proxyWith ρ e
    eval' ρ' e1
  evalDomain ρ (Proj2 e) = do
    VWith ρ' _ e2 <- evalToValDom proxyWith ρ e
    eval' ρ' e2



-- State Monad -------------------------------------------------

data LState' :: LType sig -> LType sig ~> LType sig
type instance Apply (LState' s) t = s ⊸ s ⊗ t

type LState s t = LState' s @@ t
type HasLStateDom lang = (WFDomain TensorDom lang, WFDomain LowerDom lang, 
                          WFDomain OneDom lang, WFDomain LolliDom lang) 

runLState :: HasLStateDom lang
          => LinT lang (LState' s) a -> Lift lang s -> Lift lang (s ⊗ Lower a)
runLState st s = Suspend $ forceT st `app` force s

execLState :: HasLStateDom lang 
           => LinT lang (LState' s) a -> Lift lang s -> Lift lang s
execLState st s = Suspend $ 
    forceT st `app` force s `letPair` \(s',a) ->
    a >! \_ ->
    s'

evalLState :: HasLStateDom lang
           => LinT lang (LState' s) a
           -> Lift lang s
           -> Lift lang (s ⊸ One) -- a way to eliminate the state
           -> Lin lang a
evalLState st s f = suspendL $
    force (runLState st s) `letPair` \(s',a) ->
    force f `app` s' `letUnit` a

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
    fs `app` r `letPair` \(r,s) ->
    r ⊗ (f `app` s)

instance HasLStateDom lang => LApplicative lang (LState' r) where
  lpure = λ $ \s -> λ $ \r -> r ⊗ s

  llift :: forall s t. 
           LExp lang 'Empty (LState r (s ⊸ t) ⊸ LState r s ⊸ LState r t)
  llift = λ $ \ff -> λ $ \fs -> λ $ \r ->
    ff `app` r `letPair` \ (r,f) -> 
    fs `app` r `letPair` \ (r,s) ->
    r ⊗ (f `app` s)

instance HasLStateDom lang => LMonad lang (LState' s) where
  lbind = λ $ \ ms -> λ $ \ f -> λ $ \r -> 
     ms `app` r `letPair` \(r,s) -> 
     f `app` s `app` r

-- Linearity monad transformer
data LinT lang (m :: LType sig ~> LType sig) :: * -> * where
  LinT :: Lift lang (m @@ Lower a) -> LinT lang m a

forceT :: LinT lang m a -> LExp lang 'Empty (m @@ Lower a)
forceT (LinT e) = force e
suspendT :: LExp lang 'Empty (m @@ Lower a) -> LinT lang m a
suspendT = LinT . Suspend

lowerT :: (WFDomain LolliDom lang, WFDomain LowerDom lang)
       => LExp lang 'Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
lowerT = λ $ \g -> λ $ \ x -> 
          g >! \f ->
          x >! \a -> put $ f a

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
      f' = λ $ \ x -> x >! (forceT . f)
      mb :: LExp lang 'Empty (m @@ Lower b)
      mb = lbind @lang @m @(Lower a) @(Lower b) `app` forceT x `app` f'   






-- concrete examples

type MultiplicativeProductSig m = 'Sig m '[ OneSig, TensorSig, LolliSig ]
type MultiplicativeProductDom m = ('Lang '[ OneDom, TensorDom, LolliDom ] 
    :: Lang (MultiplicativeProductSig m) )

swapMP :: Monad m => Lift (MultiplicativeProductDom m) (s ⊗ t ⊸ t ⊗ s)
swapMP = Suspend . λ $ \ pr ->
    pr `letPair` \(x,y) ->
    y ⊗ x




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
evalVal (Lin (Suspend e)) = eval e

run :: forall sig (lang :: Lang sig) a. 
       Domain LowerDom lang
    => Lin lang a -> SigEffect sig a
run e = do
  VPut a <- evalToValDom proxyLower SEmpty $ forceL e
  return a
