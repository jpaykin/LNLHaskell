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
  eval     :: Monad (Effect sig) => LExp sig γ τ -> SCtx sig γ -> Effect sig (LVal sig τ)
  fromVPut :: Monad (Effect sig) => LVal sig (Lower a) -> Effect sig a


-- For each domain:

-- 1) Declare a data type
data LolliSig ty = LolliSig ty ty

-- 2) embed it into LType
type (σ :: LType) ⊸ (τ :: LType) = MkLType ('LolliSig σ τ)
infixr 0 ⊸

-- 3) Define an interface
class HasLolli (sig :: Sig) where
  λ :: forall x σ γ γ' γ'' τ.
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp sig γ'' σ -> LExp sig γ' τ) -> LExp sig γ (σ ⊸ τ)
  (^) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (σ :: LType) (τ :: LType).
         CMerge γ1 γ2 γ
      => LExp sig γ1 (σ ⊸ τ) -> LExp sig γ2 σ -> LExp sig γ τ


letin :: (HasLolli sig, CAddCtx x σ γ2 γ2'
         , CSingletonCtx x σ γ2'', CMerge γ1 γ2 γ, x ~ Fresh γ2)
      => LExp sig γ1 σ -> (LExp sig γ2'' σ -> LExp sig γ2' τ) -> LExp sig γ τ
letin e f = λ f ^ e

-- One -----------------------------------------------
data OneSig ty = OneSig
type One = (MkLType 'OneSig :: LType)

class HasOne sig where
  unit :: LExp sig (Empty :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => LExp sig γ1 One -> LExp sig γ2 τ -> LExp sig γ τ

λunit :: (HasOne sig, HasLolli sig, WFFresh One γ)
      => (() -> LExp sig γ τ) -> LExp sig γ (One ⊸ τ)
λunit f = λ $ \x -> x `letUnit` f ()

-- Tensor ---------------------------------------------  

type Var sig x σ = LExp sig (Singleton x σ) σ

data TensorSig ty = TensorSig ty ty
type (σ1 :: LType) ⊗ (σ2 :: LType) = MkLType ('TensorSig σ1 σ2)

-- Exp = Ctx -> LType -> Type
class HasTensor sig where
  (⊗) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (τ1 :: LType) (τ2 :: LType).
         CMerge γ1 γ2 γ
      => LExp sig γ1 τ1 -> LExp sig γ2 τ2 -> LExp sig γ (τ1 ⊗ τ2)
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => LExp sig γ1 (σ1 ⊗ σ2)
      -> ((LExp sig γ21 σ1, LExp sig γ22 σ2) -> LExp sig γ2'' τ)
      -> LExp sig γ τ

λpair :: (HasTensor sig, HasLolli sig
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

class HasPar sig where
  inPar :: (CMerge γ1 γ2 γ, CMerge γ21 γ22 γ2)
        => LExp sig γ1 (σ ⅋ τ)
        -> LExp sig γ21 (σ ⊸ σ')
        -> LExp sig γ22 (τ ⊸ τ')
        -> LExp sig γ   (σ' ⅋ τ')


-- Additive Sum ---------------------------------------

data PlusSig ty = PlusSig ty ty
type (⊕) (σ :: LType) (τ :: LType) = MkLType ('PlusSig σ τ)

class HasPlus sig where
  inl :: LExp sig γ τ1 -> LExp sig γ (τ1 ⊕ τ2)
  inr :: LExp sig γ τ2 -> LExp sig γ (τ1 ⊕ τ2)
  caseof :: ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => LExp sig γ1 (σ1 ⊕ σ2)
        -> (LExp sig γ21' σ1 -> LExp sig γ21 τ)
        -> (LExp sig γ22' σ2 -> LExp sig γ22 τ)
        -> LExp sig γ τ


-- Additive Product -------------------------------------

data WithSig ty = WithSig ty ty
type (σ :: LType) & (τ :: LType) = MkLType ('WithSig σ τ)

class HasWith sig where
  (&) :: LExp sig γ τ1 -> LExp sig γ τ2 -> LExp sig γ (τ1 & τ2)
  proj1 :: LExp sig γ (τ1 & τ2) -> LExp sig γ τ1
  proj2 :: LExp sig γ (τ1 & τ2) -> LExp sig γ τ2

-- Zero ------------------------------------------------

data ZeroSig ty = ZeroSig
type Zero = MkLType 'ZeroSig

class HasZero sig where
  absurd :: CMerge γ1 γ2 γ => LExp sig γ1 Zero -> LExp sig γ τ

-- Top ------------------------------------------------

data TopSig ty = TopSig
type Top = MkLType 'TopSig

class HasTop sig where
  abort :: LExp sig γ Top

-- Lower ----------------------------------------------
data LowerSig ty = LowerSig Type
type Lower a = (MkLType ('LowerSig a) :: LType)

class HasLower sig where
  put  :: a -> LExp sig Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => LExp sig γ1 (Lower a) -> (a -> LExp sig γ2 τ) -> LExp sig γ τ

λbang :: ( HasLower sig, HasLolli sig, WFFresh (Lower a) γ)
   => (a -> LExp sig γ τ) -> LExp sig γ (Lower a ⊸ τ)
λbang f = λ $ \x -> x >! f

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

type HasBang sig = (HasLower sig)
type HasILL sig = (HasLolli sig, HasBang sig)
type HasMILL sig = (HasILL sig, HasOne sig, HasTensor sig)
type HasMELL sig = (HasMILL sig, HasLower sig)
type HasMALL sig = (HasMILL sig, HasWith sig, HasPlus sig)

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

id :: HasILL sig => Lift sig (σ ⊸ σ)
id = suspend . λ $ \x -> x

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


---------------------------------------------------------------
-- Linearity Monad --------------------------------------------
---------------------------------------------------------------

newtype Lin sig a = Lin (Lift sig (Lower a))

instance HasLift sig (Lower α) (Lin sig α) where
    suspend = Lin . suspend
    force (Lin x) = force x


--suspendL :: LExp sig Empty (Lower a) -> Lin sig a
--suspendL = Lin . suspend

--forceL :: Lin sig a -> LExp sig Empty (Lower a)
--forceL (Lin x) = force x

instance (HasLower sig) => Functor (Lin sig) where
  fmap f e = suspend $ force e >! (put . f)
instance (HasLower sig) => Applicative (Lin sig) where
  pure = suspend . put
  f <*> e = suspend $ force e >! \a ->
                       force f >! \g ->
                       put $ g a
instance (HasLower sig) => Monad (Lin sig) where
  e >>= f = suspend $ force e >! \a ->
                       force (f a)

run :: forall sig a. (Monad (Effect sig), Eval sig) => Lin sig a -> Effect sig a
run e = eval (force e) SEmpty >>= fromVPut

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
            => LinT sig (LState' σ) a -> Lift sig σ -> Lift sig σ
execLStateT st s = suspend $ force (runLStateT st s) `letPair` \(s,a) -> 
                             a >! \_ -> s

evalLStateT :: HasMILL sig
            => LinT sig (LState' σ) a -> Lift sig σ 
            -> Lift sig (σ ⊸ One) -> Lin sig a
evalLStateT st s free = suspend $ force (runLStateT st s) `letPair` \(s,a) ->
                                   force free ^ s `letUnit` a


class HasVar (sig :: Sig) where
  var :: forall x (σ :: LType) (γ :: Ctx). 
         CSingletonCtx x σ γ => LExp sig γ σ

{-


---------------------------------------------------------------
-- Patterns ---------------------------------------------------
---------------------------------------------------------------





data Pat γin γout γsing σ where
--  X    :: exp γ σ -> Pat exp γ σ
  U    :: Pat γ γ Empty One
  Put  :: a -> Pat γ γ Empty (Lower a)
  Pair :: (CMerge γ1 γ2 γ, WFFresh σ1 γ1, WFFresh σ2 γ2)
       => Pat γin1 γout1 γ1 σ1 -> Pat γout1 γout2 γ2 σ2 
       -> Pat γin1 γout2 γ (σ1 ⊗ σ2)
  Inl  :: Pat γin γout γ σ1 -> Pat γin γout γ (σ1 ⊕ σ2)
  Inr  :: Pat γin γout γ σ2 -> Pat γin γout γ (σ1 ⊕ σ2)

type PatMatch exp γin σ τ = forall γout γ. 
        CMerge γin γ γout => Pat γin γout γ σ -> exp γout τ

class Matchable exp σ where 
  pat :: Pat γin γout γ σ -> exp γ σ
  λcase :: (HasLolli exp, WFVar (Fresh γin) σ γin)
        => PatMatch exp γin σ τ -> exp γin (σ ⊸ τ)

match :: (Matchable exp σ, HasLolli exp, CMerge γ1 γ2 γ, WFVar (Fresh γ2) σ γ2)
      => exp γ1 σ -> PatMatch exp γ2 σ τ -> exp γ τ
match e f = (λcase f) ^ e


instance HasOne exp => Matchable exp One where
  pat U = unit
  λcase f = λ $ \x -> x `letUnit` f U

instance HasLower exp => Matchable exp (Lower a) where
  pat (Put a) = put a
  λcase f = λ $ \x -> x >! \a -> f (Put a)

instance (HasTensor exp, Matchable exp σ1, Matchable exp σ2) 
      => Matchable exp (σ1 ⊗ σ2) where
  pat (Pair p1 p2) = pat p1 ⊗ pat p2
--  λcase f = λ $ \x -> x `letPair` \(x1,x2) -> 
--    x1 `match` \(p1 :: Pat γin1 γout1 γ1 σ1) -> 
--    x2 `match` \(p2 :: Pat γin1 γout1 γ2 σ2) -> f (Pair p1 p2)


instance (HasPlus exp, Matchable exp σ1, Matchable exp σ2) 
      => Matchable exp (σ1 ⊕ σ2) where
  pat (Inl p1) = inl $ pat p1
  pat (Inr p2) = inr $ pat p2
--  λcase f = λ $ \x -> caseof x (\y -> y `match` \p -> f (Inl p))
--                               (\y -> y `match` \p -> f (Inr p))


--swap :: (HasTensor exp, Matchable exp σ1, Matchable exp σ2) 
--     => Lift exp (σ1 ⊗ σ2 ⊸ σ2 ⊗ σ1)
--swap = suspend . λcase $ \(Pair p1 p2) -> pat p2 ⊗ pat p1

--instance Matchable exp One where
--  λcase (Match f) = λ $ \x -> x `letUnit` f U

--instance (Matchable exp σ1, Matchable exp σ2) => Matchable exp (σ1 ⊗ σ2) where
--  λcase (Match f) = λ $ \x -> x `letPair` \(y,z) -> f (Pair (X y) (X z))

--foo = λcase . Match $ \ Pair p1 p2 -> pat p2 ⊗ pat p1


-- data PatMatch exp γ (σs :: [LType]) τ where
--   X   :: (CAddTypes σs γ γ', x ~ Fresh γ)
--       => (Tuple γ σs -> exp γ' τ) -> PatMatch exp γ σs τ
--   Put :: (a -> exp γ τ) -> PatMatch exp γ (Lower a) τ
--   Pair :: (CAddCtx x σ1 γ γ', x ~ Fresh γ)
--        => PatMatch2 exp γ σ1 σ2 τ -> PatMatch exp γ (σ1 ⊗ σ2) τ
  

-- λcase :: HasLolli exp => PatMatch exp γ σ τ -> exp γ (σ ⊸ τ)
-- λcase (X f)   = λ f
-- λcase (Put f) = λ $ \x -> x >! f
-- λcase (Pair 

-- foo :: (Matchable exp (σ1 ⊗ σ2), HasTensor exp, HasLolli exp)
--     => exp Empty (σ1 ⊗ σ2 ⊸ σ2 ⊗ σ1)
-- foo = λcase . Pair . V $ \x1 -> λ $ \x2 -> x2 ⊗ x1




type family AddFresh γ (σ :: LType) :: Ctx where
  AddFresh γ (MkLType ('TensorSig σ τ)) = 
    Merge12 (AddFresh γ σ) (Merge12 γ (AddFresh γ σ))
  AddFresh γ (MkLType ('LowerSig a))    = 'Empty
  AddFresh γ σ                          = Singleton (Fresh γ) σ

class CAddFresh γ σ γ' | γ σ -> γ', γ' σ -> γ

--class Matchable exp σ where
--  pat :: CAddFresh γ σ γ' => Pat σ -> exp γ' σ
--  λcase :: (CAddFresh γ σ γ', CMerge γ γ' γ'')
--        => (Pat σ -> exp γ'' τ) -> exp γ (σ ⊸ τ)

--foo :: forall (exp :: Exp) σ τ. 
--       (HasTensor exp, Matchable exp σ, Matchable exp τ, Matchable exp (σ ⊗ τ))
--    => Lift exp (σ ⊗ τ ⊸ τ ⊗ σ)
--foo = Suspend . λcase $ \(x,y) -> pat y ⊗ pat x


{-
data Bang a = Bang a
type family Pat (σ :: LType) where
    Pat ('LType _ ('TensorSig σ τ)) = (Pat σ, Pat τ)
    Pat ('LType _ ('PlusSig σ τ))   = Either (Pat σ) (Pat τ)
    Pat ('LType _ ('LowerSig a))    = Bang a
--  Pat _                           = 

-- FreshCtx γ σ is a context γ extended with fresh variables for every pattern variable in σ
class FreshCtx (γ :: Ctx) (σ :: LType) (γ' :: Ctx)
instance (pf ~ IsInSig TensorSig, FreshCtx γ σ1 γ0, FreshCtx γ0 σ2 γ')
      => FreshCtx (γ :: Ctx) ('LType pf ('TensorSig σ1 σ2)) γ'
-}


--type family   FreshCtx (γ :: Ctx) (σ :: LType) :: Ctx where
--    FreshCtx γ ('LType _ ('TensorSig σ τ)) = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ ('LType _ ('PlusSig σ τ))   = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ σ                           = AddFresh γ σ

--class (Matchable' exp (Div γout γin) σ (Pat σ), CMerge γin (Div γout γin) γout) 
--    => Matchable exp γin γout σ 
--type Matchable (exp :: Exp) σ = 
--    (WFCtx (FreshCtx 'Empty σ), Matchable' exp (FreshCtx 'Empty σ) σ (Pat σ))

{-
type Matchable exp σ = Matchable' exp σ (Pat σ)
-- essentially saying that pat ≅ exp (FreshCtx Empty σ) σ
class Matchable' (exp :: Exp) σ pat where
  pat   :: FreshCtx 'Empty σ γ => pat -> exp γ σ
  λcase :: (FreshCtx γ σ γ')
        => (pat -> exp γ' τ) -> exp γ (σ ⊸ τ)
-}

-- γ0 is a context of variables not to use
-- class HasLolli exp 
--    => Matchable' (exp :: Exp) (γ :: Ctx)
--                  (σ :: LType) (pat :: Type) where
--   pat   :: pat -> exp γ σ
--   λcase :: forall γ0 γ' τ. 
--            CMerge γ γ0 γ' => (pat -> exp γ' τ) -> exp γ0 (σ ⊸ τ)

--  match :: (CMerge γ1 γ2 γ', CMerge γ γ2 γ2')
--        => exp γ1 σ -> (pat -> exp γ2' τ) -> exp γ' τ
--  match e f = λcase f ^ e

--instance ( CMerge γ1 γ2 γ, HasTensor exp
--         , Matchable' exp γ1 σ1 pat1, Matchable' exp γ2 σ2 pat2
--         , τ ~ (σ1 ⊗ σ2) )
--      => Matchable' (exp :: Exp) γ τ (pat1,pat2) where

--   pat (p1,p2) = (pat @_ @_ @γ1 @σ1 p1) ⊗ (pat @_ @_ @γ2 @σ2 p2)

--   λcase :: forall γ0 γ' ρ.
--            CMerge γ0 γ γ' => ((pat1,pat2) -> exp γ' ρ) -> exp γ0 (σ1 ⊗ σ2 ⊸ ρ)
--   λcase f = uncurry f'
 --    uncurry @exp $ λcase (\p1 -> λcase @_ @exp (\p2 -> f (p1,p2)))
--     where
---       f' :: exp γ0 (σ1 ⊸ σ2 ⊸ ρ)
--       f' = undefined -- λcase @_ @exp @γ1 @σ1 @pat1 $ \p1 -> _
    

--  match :: forall γ1 γ2 γ' γ2' τ. (CMerge γ1 γ2 γ', CMerge γ γ2 γ2')
--        => exp γ1 (σ1 ⊗ σ2) -> ((pat1,pat2) -> exp γ2' τ) -> exp γ' τ
--  match = undefined
--  match e f   = letPair @_ @_ @_ @_ @_ @_ @_ @γ1 e $ \(x1,x2) ->
--                match @_ @exp x1 $ \p1 ->
--                match @_ @exp x2 $ \p2 ->
--                f (p1,p2)


--instance (HasPlus exp, Matchable' exp γ σ1 pat1, Matchable' exp γ σ2 pat2, τ ~ (σ1 ⊕ σ2))
--      => Matchable' exp γ τ (Either pat1 pat2) where
--  pat (Left  p) = inl $ pat p
--  pat (Right p) = inr $ pat p

-- Example programs

--foo :: forall (exp :: Exp) σ τ. 
--       (HasTensor exp, Matchable exp σ, Matchable exp τ)
--    => Lift exp (σ ⊗ τ ⊸ τ ⊗ σ)
--foo = Suspend . λcase $ \(x,y) -> pat y ⊗ pat x

-}
