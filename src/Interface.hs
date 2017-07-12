{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             InstanceSigs, TypeApplications, 
             ScopedTypeVariables, UndecidableInstances,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             TypeFamilyDependencies, LambdaCase
#-}

module Interface where
 
import Prelude hiding ((^), uncurry)
import Prelim hiding (One)
import Types
import Classes

import Data.Kind
import qualified Data.Singletons as Sing
type (~>) a b = Sing.TyFun a b -> Type


class Eval (sig :: Sig) where
  eval     :: Monad (Effect sig) => LExp sig γ τ -> ECtx sig γ -> Effect sig (LVal sig τ)
  fromVPut :: Monad (Effect sig) => LVal sig (Lower a) -> Effect sig a


-- For each domain:

-- 1) Declare a data type
data LolliSig ty = LolliSig ty ty

-- 2) embed it into LType
type (σ :: LType) ⊸ (τ :: LType) = MkLType ('LolliSig σ τ)
infixr 0 ⊸

-- 3) Define an interface
class HasLolli (exp :: Exp) where
  λ :: forall x σ γ γ' γ'' τ.
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (exp γ'' σ -> exp γ' τ) -> exp γ (σ ⊸ τ)
  (^) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (σ :: LType) (τ :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ) -> exp γ2 σ -> exp γ τ


letin :: (HasLolli exp, CAddCtx x σ γ2 γ2'
         , CSingletonCtx x σ γ2'', CMerge γ1 γ2 γ, x ~ Fresh γ2)
      => exp γ1 σ -> (exp γ2'' σ -> exp γ2' τ) -> exp γ τ
letin e f = λ f ^ e

-- One -----------------------------------------------
data OneSig ty = OneSig
type One = (MkLType 'OneSig :: LType)

class HasOne exp where
  unit :: exp (Empty :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ

λunit :: (HasOne (LExp sig), HasLolli (LExp sig), WFFresh One γ)
      => (() -> LExp sig γ τ) -> LExp sig γ (One ⊸ τ)
λunit f = λ $ \x -> x `letUnit` f ()

-- Tensor ---------------------------------------------  

type Var sig x σ = LExp sig (SingletonF x σ) σ

data TensorSig ty = TensorSig ty ty
type (σ1 :: LType) ⊗ (σ2 :: LType) = MkLType ('TensorSig σ1 σ2)

-- Exp = Ctx -> LType -> Type
class HasTensor exp where
  (⊗) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (τ1 :: LType) (τ2 :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 τ1 -> exp γ2 τ2 -> exp γ (τ1 ⊗ τ2)
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => exp γ1 (σ1 ⊗ σ2)
      -> ((exp γ21 σ1, exp γ22 σ2) -> exp γ2'' τ)
      -> exp γ τ

λpair :: (HasTensor (LExp sig), HasLolli (LExp sig)
         , CSingletonCtx x1 σ1 γ1, CSingletonCtx x2 σ2 γ2
         , CAddCtx x1 σ1 γ γ', CAddCtx x2 σ2 γ' γ''
         , x1 ~ Fresh γ, x2 ~ Fresh γ'
         , WFVar x1 (σ1 ⊗ σ2) γ, WFVar x2 (σ1 ⊗ σ2) γ
         )
        => ((LExp sig γ1 σ1, LExp sig γ2 σ2) -> LExp sig γ'' τ) -> LExp sig γ (σ1⊗σ2 ⊸ τ)
λpair f = λ $ \z -> z `letPair` f


-- Bottom -------------------------------------------

data BottomSig ty = BottomSig
type Bottom = (MkLType 'BottomSig :: LType)

-- Par ----------------------------------------------

data ParSig ty = ParSig ty ty
type σ ⅋ τ = MkLType ('ParSig σ τ)

class HasPar exp where
  inPar :: (CMerge γ1 γ2 γ, CMerge γ21 γ22 γ2)
        => exp γ1 (σ ⅋ τ)
        -> exp γ21 (σ ⊸ σ')
        -> exp γ22 (τ ⊸ τ')
        -> exp γ   (σ' ⅋ τ')


-- Additive Sum ---------------------------------------

data PlusSig ty = PlusSig ty ty
type (⊕) (σ :: LType) (τ :: LType) = MkLType ('PlusSig σ τ)

class HasPlus exp where
  inl :: exp γ τ1 -> exp γ (τ1 ⊕ τ2)
  inr :: exp γ τ2 -> exp γ (τ1 ⊕ τ2)
  caseof :: ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => exp γ1 (σ1 ⊕ σ2)
        -> (exp γ21' σ1 -> exp γ21 τ)
        -> (exp γ22' σ2 -> exp γ22 τ)
        -> exp γ τ


-- Additive Product -------------------------------------

data WithSig ty = WithSig ty ty
type (σ :: LType) & (τ :: LType) = MkLType ('WithSig σ τ)

class HasWith exp where
  (&) :: exp γ τ1 -> exp γ τ2 -> exp γ (τ1 & τ2)
  proj1 :: exp γ (τ1 & τ2) -> exp γ τ1
  proj2 :: exp γ (τ1 & τ2) -> exp γ τ2

-- Zero ------------------------------------------------

data ZeroSig ty = ZeroSig
type Zero = MkLType 'ZeroSig

class HasZero exp where
  absurd :: CMerge γ1 γ2 γ => exp γ1 Zero -> exp γ τ

-- Top ------------------------------------------------

data TopSig ty = TopSig
type Top = MkLType 'TopSig

class HasTop exp where
  abort :: exp γ Top

-- Lower ----------------------------------------------
data LowerSig ty = LowerSig Type
type Lower a = (MkLType ('LowerSig a) :: LType)

class HasLower exp where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ

λbang :: ( HasLower (LExp sig), HasLolli (LExp sig), WFFresh (Lower a) γ)
   => (a -> LExp sig γ τ) -> LExp sig γ (Lower a ⊸ τ)
λbang f = λ $ (>! f)

-- Lift --------------------------------------------------

class HasLift sig τ lift | lift -> sig τ where
  suspend :: LExp sig Empty τ -> lift
  force   :: lift -> LExp sig Empty τ

data Lift (sig :: Sig) (τ :: LType) = Suspend (LExp sig Empty τ)

instance HasLift sig τ (Lift sig τ) where
  suspend = Suspend
  force (Suspend e) = e


--instance HasLift sig Lin (Lower α) where

-- Families of linear languages --------------------------

type HasBang sig = (HasLower (LExp sig))
type HasILL sig = (HasLolli (LExp sig), HasBang sig)
type HasMILL sig = (HasILL sig, HasOne (LExp sig), HasTensor (LExp sig))
type HasMALL sig = (HasMILL sig, HasWith (LExp sig), HasPlus (LExp sig))

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

idL :: HasILL sig => Lift sig (σ ⊸ σ)
idL = suspend . λ $ \x -> x

sApp :: HasILL sig => Lift sig (σ ⊸ τ) -> Lift sig σ -> Lift sig τ
sApp f e = suspend $ force  f ^ force e

uncurryL :: HasMILL sig => Lift sig ((σ1 ⊸ σ2 ⊸ τ) ⊸ σ1 ⊗ σ2 ⊸ τ)
uncurryL = suspend . λ $ \f -> λ $ \x -> 
    x `letPair` \(x1,x2) -> 
    f ^ x1 ^ x2
uncurry :: (HasMILL sig, WFCtx γ) => LExp sig γ (σ1 ⊸ σ2 ⊸ τ) -> LExp sig γ (σ1 ⊗ σ2 ⊸ τ)
uncurry e = force uncurryL ^ e


composeL :: HasMILL sig
         => Lift sig ((τ ⊸ ρ) ⊸ (σ ⊸ τ) ⊸ (σ ⊸ ρ))
composeL = suspend . λ $ \g -> λ $ \f -> λ $ \x -> g ^ (f ^ x)
compose :: (HasMILL sig, CMerge γ1 γ2 γ)
        => LExp sig γ1 (τ ⊸ ρ) -> LExp sig γ2 (σ ⊸ τ) -> LExp sig γ (σ ⊸ ρ)
compose g f = force composeL ^ g ^ f

--------------------------------------------------------------
-- Comonad ---------------------------------------------------
--------------------------------------------------------------

type Bang sig σ = Lower (Lift sig σ)

extract :: HasILL sig => Lift sig (Bang sig τ ⊸ τ)
extract = suspend . λbang $ \x → force x

duplicate :: HasILL sig => Lift sig (Bang sig τ ⊸ Bang sig (Bang sig τ))
duplicate = suspend . λbang $ put . suspend . put

---------------------------------------------------------------
-- Linearity Monad --------------------------------------------
---------------------------------------------------------------

newtype Lin sig a = Lin (Lift sig (Lower a))

instance HasLift sig (Lower α) (Lin sig α) where
    suspend = Lin . suspend
    force (Lin e) = force e


--suspendL :: LExp sig Empty (Lower a) -> Lin sig a
--suspendL = Lin . suspend

--forceL :: Lin sig a -> LExp sig Empty (Lower a)
--forceL (Lin x) = force x

instance (HasLower (LExp sig)) => Functor (Lin sig) where
  fmap f e = suspend $ force e >! (put . f)
instance (HasLower (LExp sig)) => Applicative (Lin sig) where
  pure = suspend . put
  f <*> e = suspend $ force e >! \a ->
                       force f >! \g ->
                       put $ g a
instance (HasLower (LExp sig)) => Monad (Lin sig) where
  e >>= f = suspend $ force e >! \a ->
                       force (f a)

run :: forall sig a. (Monad (Effect sig), Eval sig) => Lin sig a -> Effect sig a
run e = eval (force e) eEmpty >>= fromVPut

---------------------------------------------------------------
-- Linearity Monad Transformer --------------------------------
---------------------------------------------------------------

newtype LinT sig (f :: LType ~> LType) a = LinT (Lift sig (f @@ (Lower a)))

instance τ ~ (f @@ (Lower α)) => HasLift sig τ (LinT sig f α) where
    suspend = LinT . suspend
    force (LinT x) = force x

--suspendT :: LExp sig Empty (f @@ (Lower a)) -> LinT sig f a
--suspendT = LinT . suspend

--forceT :: forall f sig a. LinT sig f a -> LExp sig Empty (f @@ (Lower a))
--forceT (LinT e) = force e

lowerT :: HasILL sig => (a -> b) -> LExp sig Empty (Lower a ⊸ Lower b)
lowerT f = λ $ \x -> x >! \a -> put $ f a

lowerT2 :: HasILL sig => (a -> b -> c) 
        -> LExp sig Empty (Lower a ⊸ Lower b ⊸ Lower c)
lowerT2 f = λ $ \x -> x >! \a ->
            λ $ \y -> y >! \b -> put $ f a b

instance (HasILL sig, LFunctor sig f) => Functor (LinT sig f) where
    fmap g x = suspend $ lowerT g <$$> force x
instance (HasILL sig, LApplicative sig f) => Applicative (LinT sig f) where
    pure a = suspend $ lpure (put a)

    -- force f :: f (Lower (a -> b))
    -- force x :: f (Lower a) 
    -- lowerT' <$$> force f :: f (Lower a ⊸ Lower b)
    (<*>) :: LinT sig f (a -> b) -> LinT sig f a -> LinT sig f b
    f <*> x = suspend $ (lowerT' <$$> force f) <**> force x
      where
        lowerT' :: LExp sig Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
        lowerT' = λ $ \f -> f >! lowerT
instance (HasILL sig, LMonad sig f) => Monad (LinT sig f) where
    x >>= f = suspend $ force x =>>= (λ $ \y -> y >! (force . f))

--------------------------------------------------------------
-- LMonad ----------------------------------------------------
--------------------------------------------------------------

class LFunctor sig (f :: LType ~> LType) where
  (<$$>) :: CMerge γ1 γ2 γ 
         => LExp sig γ1 (σ ⊸ τ) -> LExp sig γ2 (f @@ σ) -> LExp sig γ (f @@ τ)
class LFunctor sig f => LApplicative sig f where
  lpure  :: WFCtx γ => LExp sig γ τ -> LExp sig γ (f @@ τ)
  (<**>) :: CMerge γ1 γ2 γ
         => LExp sig γ1 (f @@ (σ ⊸ τ)) -> LExp sig γ2 (f @@ σ) -> LExp sig γ (f @@ τ)
class LApplicative sig m => LMonad sig m where
  (=>>=) :: CMerge γ1 γ2 γ
         => LExp sig γ1 (m @@ σ) -> LExp sig γ2 (σ ⊸ m @@ τ) -> LExp sig γ (m @@ τ)


-- State monad

data LState' :: LType -> LType ~> LType
type family (f :: k1 ~> k2) @@ (x :: k1) = (r :: b) | r -> f x

type instance (LState' σ) @@ τ = σ ⊸ σ ⊗ τ
type LState σ τ = LState' σ @@ τ

instance HasMILL sig => LFunctor sig (LState' ρ) where
  f <$$> e = force lfmap ^ f ^ e
    where
      lfmap :: Lift sig ((σ ⊸ τ) ⊸ LState ρ σ ⊸ LState ρ τ)
      lfmap = suspend . λ $ \f -> λ $ \x -> λ $ \r ->
        x ^ r `letPair` \(r,s) -> r ⊗ (f ^ s)
instance HasMILL sig => LApplicative sig (LState' ρ) where
  lpure e = force lpure' ^ e
    where
      lpure' :: Lift sig (σ ⊸ LState ρ σ)
      lpure' = suspend . λ $ \x -> λ $ \r -> r ⊗ x
  f <**> e = force lapp ^ e ^ f
    where
      lapp :: Lift sig (LState ρ σ ⊸ LState ρ (σ ⊸ τ) ⊸ LState ρ τ)
      lapp = suspend . λ $ \st -> λ $ \stF -> λ $ \r ->
        st ^ r `letPair` \(r,s) ->
        stF ^ r `letPair` \(r,f) ->
        r ⊗ (f ^ s)
instance HasMILL sig => LMonad sig (LState' ρ) where
  e =>>= f = force lbind ^ e ^ f
    where
      lbind :: Lift sig (LState ρ σ ⊸ (σ ⊸ LState ρ τ) ⊸ LState ρ τ)
      lbind = suspend . λ $ \st -> λ $ \f -> λ $ \ r ->
                st ^ r `letPair` \(r,s) -> f ^ s ^ r

runLStateT :: HasMILL sig 
           => LinT sig (LState' σ) a -> Lift sig σ -> Lift sig (σ ⊗ Lower a)
runLStateT st s = suspend $ force st ^ force s

execLStateT :: HasMILL sig
            => LStateT sig σ a -> Lift sig σ -> Lift sig σ
execLStateT st s = suspend $ force (runLStateT st s) `letPair` \(s,a) -> 
                             a >! \_ -> s

evalLStateT :: HasMILL sig
            => LinT sig (LState' σ) a -> Lift sig σ 
            -> Lift sig (σ ⊸ One) -> Lin sig a
evalLStateT st s free = suspend $ force (runLStateT st s) `letPair` \(s,a) ->
                                   force free ^ s `letUnit` a


-- for convenience
type LStateT sig σ α = LinT sig (LState' σ) α

class HasVar exp where
  var :: forall x (σ :: LType) (γ :: Ctx). 
         CSingletonCtx x σ γ => Sing x -> exp γ σ

-- non-examples
--discard :: HasMILL sig => Lift sig (σ ⊸ One)
--discard = suspend . λ $ \_ → unit

--dup :: HasMILL sig => Lift sig (σ ⊸ σ ⊗ σ)
--dup = suspend . λ $ \x → x ⊗ x
