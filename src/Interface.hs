{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, FlexibleContexts,
             EmptyCase, RankNTypes, TypeFamilyDependencies,
             ConstraintKinds
#-}
-- {-# OPTIONS_GHC -Wall -Wcompat #-}

module Interface where

import Data.Kind
import Data.Proxy
import Data.Singletons

import Types
import Context
import Proofs
import Classes
import Lang

var :: forall x σ g lang. CSingletonCtx x σ g
    => LExp lang g σ
var = Var $ singletonCtx @x

-- Implication ----------------------------------

data LolliSig sig where
  LolliSig :: LType sig -> LType sig -> LolliSig ty

type (⊸) (σ :: LType sig) (τ :: LType sig) = LType' sig ('LolliSig σ τ)
infixr 0 ⊸

data LolliExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Abs :: AddCtx x σ γ γ'
      -> LExp lang γ' τ
      -> LolliExp lang γ (σ ⊸ τ)
  App :: Merge γ1 γ2 γ
      -> LExp lang γ1 (σ ⊸ τ)
      -> LExp lang γ2 σ
      -> LolliExp lang γ τ
data LolliVal :: Lang sig -> LType sig -> * where
  -- The value is a closure
  VAbs :: ECtx lang γ
       -> AddCtx x σ γ γ'
       -> LExp lang γ' τ
       -> LolliVal lang (σ ⊸ τ)


type LolliDom = '(LolliExp, LolliVal)
proxyLolli = (Proxy :: Proxy LolliDom)

-- Can we make this CBN instead of CBV? Can we have both?
instance WFDomain LolliDom lang => Domain LolliDom lang where
  evalDomain ρ (Abs pfA e) = return $ VDom proxyLolli $ VAbs ρ pfA e
  evalDomain ρ (App pfM e1 e2) = do
      VDom _ (VAbs ρ' pfA e1') <- eval' ρ1 e1 --evalToValDom proxyLolli ρ1 e1
      v2              <- eval' ρ2 e2
      eval' (addSCtx pfA ρ' $ ValData v2) e1'
    where
      (ρ1,ρ2) = splitSCtx pfM ρ


instance Show (LolliExp lang g τ) where
  show (Abs pfA e) = "λ " ++ show (addToSNat pfA) ++ " . " ++ show e
  show (App _ e1 e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"

λ :: forall g lang x σ τ g' g''. 
     ( Domain LolliDom lang
     , CAddCtx x σ g g'
     , CSingletonCtx x σ g'' 
     , x ~ Fresh g)
  => (LExp lang g'' σ -> LExp lang g' τ) -> LExp lang g (σ ⊸ τ)
λ f = Dom proxyLolli $ Abs (addCtx @x) (f . Var $ singletonCtx @x) 

app :: (Domain LolliDom lang, CMerge g1 g2 g3)
    => LExp lang g1 (σ ⊸ τ)
    -> LExp lang g2 σ
    -> LExp lang g3 τ
e1 `app` e2 = Dom proxyLolli $ App merge e1 e2


letin :: forall lang x σ τ g g1 g2 g2' g2''.
         ( Domain LolliDom lang
         , CAddCtx x σ g2 g2'
         , CSingletonCtx x σ g2''
         , CMerge g1 g2 g
         , x ~ Fresh g2)
      => LExp lang g1 σ
      -> (LExp lang g2'' σ -> LExp lang g2' τ)
      -> LExp lang g τ
letin e f = λ f `app` e

-- Sanity check examples 

ex :: Domain LolliDom lang => LExp lang 'Empty ((σ ⊸ τ) ⊸ σ ⊸ τ)
ex = λ (\x -> λ $ \y -> x `app` y)

--ex2 :: Domain LolliDom lang => LExp lang 'Empty (σ ⊸ τ ⊸ σ)
--ex2 = λ $ \x -> λ $ \y -> x

--ex3 :: (Domain LolliDom lang, Domain TensorDom lang) => LExp lang 'Empty (σ ⊸ σ ⊗ σ)
--ex3 = λ $ \x -> x ⊗ x

-- apply an expression to a value
-- this is conbined with evaluation
evalApplyValue :: forall sig (lang :: Lang sig) g σ τ.
                  Domain LolliDom lang
               => ECtx lang g -> LExp lang g (σ ⊸ τ) -> LVal lang σ 
               -> SigEffect sig (LVal lang τ)
evalApplyValue ρ e v = eval' ρ' $ Dom proxyLolli $ App pfM e $ Var pfS
  where
    pfS :: SingletonCtx (Fresh g) σ (Singleton (Fresh g) σ)
    pfS = singSing $ knownFresh ρ 

    ρ' :: ECtx lang (Add (Fresh g) σ g)
    ρ' = addFreshSCtx ρ (ValData v)

    pfM :: Merge g (Singleton (Fresh g) σ) (Add (Fresh g) σ g)
    pfM = mergeAddFresh @σ ρ




-- DEFINING DOMAINS ---------------------------------

-- One ---------------------------------------

data OneSig sig where
  OneSig :: OneSig sig

type One = (LType' sig 'OneSig :: LType sig)

data OneExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Unit :: OneExp lang 'Empty One
  LetUnit :: Merge g1 g2 g -> LExp lang g1 One -> LExp lang g2 τ -> OneExp lang g τ

data OneVal :: forall sig. Lang sig -> LType sig -> * where
  VUnit :: OneVal lang One

type OneDom = '(OneExp,OneVal)

proxyOne :: Proxy OneDom
proxyOne = Proxy

instance Show (OneExp lang g τ) where
  show Unit = "()"
  show (LetUnit _ e1 e2) = "let () = " ++ show e1 ++ " in " ++ show e2

unit :: Domain OneDom lang
     => LExp lang 'Empty One
unit = Dom proxyOne Unit

letUnit :: (Domain OneDom lang, CMerge g1 g2 g)
        => LExp lang g1 One -> LExp lang g2 τ -> LExp lang g τ
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

type (⊗) (σ :: LType sig) (τ :: LType sig) = LType' sig ('TensorSig σ τ)

data TensorExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Pair :: Merge g1 g2 g
       -> LExp lang g1 τ1 -> LExp lang g2 τ2 -> TensorExp lang g (τ1 ⊗ τ2)
  LetPair :: Merge g1 g2'' g -> AddCtx x1 σ1 g2'' g2' -> AddCtx x2 σ2 g2' g2
          -> LExp lang g1 (σ1 ⊗ σ2) -> LExp lang g2 τ -> TensorExp lang g τ
data TensorVal :: Lang sig -> LType sig -> * where
  VPair :: LVal lang τ1 -> LVal lang τ2 -> TensorVal lang (τ1 ⊗ τ2)

type TensorDom  = '(TensorExp, TensorVal)

proxyTensor :: Proxy TensorDom
proxyTensor = Proxy

instance Show (TensorExp lang g τ) where
  show (Pair _ e1 e2) = "(" ++ show e1 ++ ", " ++ show e2 ++ ")"
  show (LetPair _ pfA1 pfA2 e e') = "let (" ++ show (addToSNat pfA1) ++ ", " ++ show (addToSNat pfA2)
    ++ ") = " ++ show e ++ " in " ++ show e'

(⊗) :: (Domain TensorDom lang, CMerge g1 g2 g)
     => LExp lang g1 σ1 -> LExp lang g2 σ2 -> LExp lang g (σ1 ⊗ σ2)
e1 ⊗ e2 = Dom proxyTensor $ Pair merge e1 e2

letPair :: forall sig (lang :: Lang sig) x1 x2 g g1 g2 g2' g2'' g21 g22 σ1 σ2 τ.
         ( Domain TensorDom lang
         , CAddCtx x1 σ1 g2'' g2'
         , CAddCtx x2 σ2 g2' g2
         , CMerge g1 g2'' g
         , CSingletonCtx x1 σ1 g21
         , CSingletonCtx x2 σ2 g22
         , x1 ~ Fresh g
         , x2 ~ Fresh2 g
         )
        => LExp lang g1 (σ1 ⊗ σ2)
        -> ((LExp lang g21 σ1, LExp lang g22 σ2) -> LExp lang g2 τ)
        -> LExp lang g τ
letPair e f = Dom proxyTensor $ LetPair merge (addCtx @x1 @_ @_ @g2') (addCtx @x2) e e'
  where
    e' :: LExp lang g2 τ
    e' = f (Var $ singletonCtx @x1, Var $ singletonCtx @x2)

vpair :: Domain TensorDom lang
      => LVal lang σ1 -> LVal lang σ2 -> LVal lang (σ1 ⊗ σ2)
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
  Suspend :: LExp lang 'Empty τ -> Lift lang τ

force :: Lift lang τ -> LExp lang 'Empty τ
force (Suspend e) = e

-- Lower -------------------------------------------------------

data LowerSig sig where
  LowerSig :: * -> LowerSig sig
type Lower a = (LType' sig ('LowerSig a) :: LType sig)

data LowerExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Put :: a -> LowerExp lang 'Empty (Lower a)
  LetBang :: Merge g1 g2 g
          -> LExp lang g1 (Lower a)
          -> (a -> LExp lang g2 τ)
          -> LowerExp lang g τ
data LowerVal :: Lang sig -> LType sig -> * where
  VPut :: a -> LowerVal lang (Lower a)

type LowerDom = '(LowerExp, LowerVal)

proxyLower :: Proxy LowerDom
proxyLower = Proxy

instance Show (LowerExp lang g τ) where
  show (Put _) = "Put"
  show (LetBang _ e _) = show e ++ ">! ??"

put :: Domain LowerDom lang
    => a -> LExp lang 'Empty (Lower a)
put a = Dom proxyLower $ Put a

(>!) :: (Domain LowerDom lang, CMerge g1 g2 g)
     => LExp lang g1 (Lower a)
     -> (a -> LExp lang g2 τ)
     -> LExp lang g τ
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
type (⊕) (σ :: LType sig) (τ :: LType sig) = LType' sig ('PlusSig σ τ)


data PlusExp :: Lang sig -> Ctx sig -> LType sig -> * where
  Inl  :: LExp lang g τ1 -> PlusExp lang g (τ1 ⊕ τ2)
  Inr  :: LExp lang g τ2 -> PlusExp lang g (τ1 ⊕ τ2)
  Case :: Merge g1 g2 g
       -> AddCtx x1 σ1 g2 g21
       -> AddCtx x2 σ2 g2 g22
       -> LExp lang g1 (σ1 ⊕ σ2)
       -> LExp lang g21 τ
       -> LExp lang g22 τ
       -> PlusExp lang g τ

data PlusVal :: Lang sig -> LType sig -> * where
  VInl :: LVal lang τ1 -> PlusVal lang (τ1 ⊕ τ2)
  VInr :: LVal lang τ2 -> PlusVal lang (τ1 ⊕ τ2)

type PlusDom = '(PlusExp, PlusVal)

proxyPlus :: Proxy PlusDom
proxyPlus = Proxy

instance Show (PlusExp lang g τ) where
  show (Inl e) = "Inl " ++ show e
  show (Inr e) = "Inr " ++ show e
  show (Case _ _ _ _ _ _) = undefined

inl :: Domain PlusDom lang
    => LExp lang g τ1 -> LExp lang g (τ1 ⊕ τ2)
inl e = Dom proxyPlus $ Inl e

inr :: Domain PlusDom lang
    => LExp lang g τ2 -> LExp lang g (τ1 ⊕ τ2)
inr e = Dom proxyPlus $ Inr e

caseof :: forall lang x σ1 σ2 g g1 g2 g21 g22 g21' g22' τ.
          ( Domain PlusDom lang
          , CAddCtx x σ1 g2 g21, CSingletonCtx x σ1 g21'
          , CAddCtx x σ2 g2 g22, CSingletonCtx x σ2 g22'
          , x ~ Fresh g
          , CMerge g1 g2 g)
       => LExp lang g1 (σ1 ⊕ σ2)
       -> (LExp lang g21' σ1 -> LExp lang g21 τ)
       -> (LExp lang g22' σ2 -> LExp lang g22 τ)
       -> LExp lang g τ
caseof e f1 f2 = Dom proxyPlus $ 
    Case merge pfA1 pfA2 e (f1 . Var $ singletonCtx @x) (f2 . Var $ singletonCtx @x)
  where
    pfA1 :: AddCtx (Fresh g) σ1 g2 g21
    pfA1 = addCtx
    pfA2 :: AddCtx (Fresh g) σ2 g2 g22
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
type (&) (σ :: LType sig) (τ :: LType sig) = LType' sig ('WithSig σ τ)

data WithExp :: Lang sig -> Ctx sig -> LType sig -> * where
  With  :: LExp lang g τ1 -> LExp lang g τ2 -> WithExp lang g (τ1 & τ2)
  Proj1 :: LExp lang g (τ1 & τ2) -> WithExp lang g τ1
  Proj2 :: LExp lang g (τ1 & τ2) -> WithExp lang g τ2
data WithVal :: Lang sig -> LType sig -> * where -- Lazy values
  VWith :: ECtx lang g -> LExp lang g τ1 -> LExp lang g τ2 -> WithVal lang (τ1 & τ2)

type WithDom = '(WithExp, WithVal)

proxyWith :: Proxy WithDom
proxyWith = Proxy

instance Show (WithExp lang g τ) where
  show = undefined

(&) :: Domain WithDom lang
    => LExp lang g τ1 -> LExp lang g τ2 -> LExp lang g (τ1 & τ2)
e1 & e2 = Dom proxyWith $ With e1 e2

proj1 :: Domain WithDom lang
      => LExp lang g (τ1 & τ2) -> LExp lang g τ1
proj1 = Dom proxyWith . Proj1

proj2 :: Domain WithDom lang
      => LExp lang g (τ1 & τ2) -> LExp lang g τ2
proj2 = Dom proxyWith . Proj2


oplus :: (Domain LolliDom lang, Domain PlusDom lang, Domain WithDom lang)
    => LExp lang 'Empty ((σ1 ⊸ τ) & (σ2 ⊸ τ) ⊸ σ1 ⊕ σ2 ⊸ τ)
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
type instance Apply (LState' σ) τ = σ ⊸ σ ⊗ τ

type LState σ τ = LState' σ @@ τ
type HasLStateDom lang = (WFDomain TensorDom lang, WFDomain LowerDom lang, 
                          WFDomain OneDom lang, WFDomain LolliDom lang) 

runLState :: HasLStateDom lang
          => LinT lang (LState' σ) a -> Lift lang σ -> Lift lang (σ ⊗ Lower a)
runLState st s = Suspend $ forceT st `app` force s

execLState :: HasLStateDom lang 
           => LinT lang (LState' σ) a -> Lift lang σ -> Lift lang σ
execLState st s = Suspend $ 
    forceT st `app` force s `letPair` \(s',a) ->
    a >! \_ ->
    s'

evalLState :: HasLStateDom lang
           => LinT lang (LState' σ) a
           -> Lift lang σ
           -> Lift lang (σ ⊸ One) -- a way to eliminate the state
           -> Lin lang a
evalLState st s f = suspendL $
    force (runLState st s) `letPair` \(s',a) ->
    force f `app` s' `letUnit` a


-- Defunctionalization from singletons library!
class LFunctor lang (f :: LType sig ~> LType sig) where
  lfmap :: LExp lang 'Empty ((σ ⊸ τ) ⊸ f @@ σ ⊸ f @@ τ)
class LFunctor lang f => LApplicative lang f where
  lpure :: LExp lang 'Empty (τ ⊸ f @@ τ)
  llift :: LExp lang 'Empty (f @@ (σ ⊸ τ) ⊸ f @@ σ ⊸ f @@ τ)
class LApplicative lang m => LMonad lang m where
  lbind :: LExp lang 'Empty (m @@ σ ⊸ (σ ⊸ m @@ τ) ⊸ m @@ τ)

instance HasLStateDom lang => LFunctor lang (LState' σ) where
  lfmap = λ $ \f -> λ $ \fs -> λ $ \r ->
    fs `app` r `letPair` \(r,s) ->
    r ⊗ (f `app` s)

instance HasLStateDom lang => LApplicative lang (LState' r) where
  lpure = λ $ \s -> λ $ \r -> r ⊗ s

  llift :: forall σ τ. 
           LExp lang 'Empty (LState r (σ ⊸ τ) ⊸ LState r σ ⊸ LState r τ)
  llift = λ $ \ff -> λ $ \fs -> λ $ \r ->
    ff `app` r `letPair` \ (r,f) -> 
    fs `app` r `letPair` \ (r,s) ->
    r ⊗ (f `app` s)

instance HasLStateDom lang => LMonad lang (LState' σ) where
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

lowerT :: (Domain LolliDom lang, Domain LowerDom lang)
       => LExp lang 'Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
lowerT = λ $ \g -> λ $ \ x -> 
          g >! \f ->
          x >! \a -> put $ f a

lowerT2 :: (Domain LolliDom lang, Domain LowerDom lang)
        => LExp lang 'Empty (Lower (a -> b -> c) ⊸ Lower a ⊸ Lower b ⊸ Lower c)
lowerT2 = λ $ \f -> λ $ \x -> λ $ \y ->
    f >! \g -> x >! \a -> y >! \b -> put $ g a b

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

swapMP :: Monad m => Lift (MultiplicativeProductDom m) (σ ⊗ τ ⊸ τ ⊗ σ)
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

-- Collections of Domains

type ILLSig = '[ LolliSig ]
type MILLSig = TensorSig ': (OneSig ': ILLSig)
type MELLSig = LowerSig ': MILLSig

type ILL  = '[ LolliDom ]
type MILL = TensorDom ': (OneDom ': ILL)
type MELL = LowerDom ': MILL

type family HasDomains (ls :: [Dom sig]) (lang :: Lang sig) where
  HasDomains '[ dom ]    lang = Domain dom lang
  HasDomains (dom ': ls) lang = (Domain dom lang, HasDomains ls lang)
