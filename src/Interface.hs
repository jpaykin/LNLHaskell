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


class Monad (Effect sig) => Eval (sig :: Sig) where
  eval :: LExp sig γ τ -> SCtx sig γ -> Effect sig (LVal sig τ)


-- For each domain:

-- 1) Declare a data type
data LolliSig ty = LolliSig ty ty

-- 2) embed it into LType
type (σ :: LType) ⊸ (τ :: LType) = MkLType ('LolliSig σ τ)
infixr 0 ⊸

-- 3) Define an interface
class HasLolli (exp :: Exp) where
  λ :: forall x (σ :: LType) (γ :: Ctx) (γ' :: Ctx) (γ'' :: Ctx) (τ :: LType).
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

class HasOne (exp :: Exp) where
  unit :: exp (Empty :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ


-- Tensor ---------------------------------------------  

type Var exp x σ = exp (Singleton x σ) σ

data TensorSig ty = TensorSig ty ty
type (σ1 :: LType) ⊗ (σ2 :: LType) = MkLType ('TensorSig σ1 σ2)

-- Exp = Ctx -> LType -> Type
class HasTensor (exp :: Exp) where
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
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ)
      => exp γ1 (σ1 ⊗ σ2)
      -> ((exp γ21 σ1, exp γ22 σ2) -> exp γ2'' τ)
      -> exp γ τ





-- Bottom -------------------------------------------

data BottomSig ty = BottomSig
type Bottom = (MkLType 'BottomSig :: LType)

-- Additive Sum ---------------------------------------

data PlusSig ty = PlusSig ty ty
type (⊕) (σ :: LType) (τ :: LType) = MkLType ('PlusSig σ τ)

class HasPlus (exp :: Exp) where
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

class HasWith (exp :: Exp) where
  (&) :: exp γ τ1 -> exp γ τ2 -> exp γ (τ1 & τ2)
  proj1 :: exp γ (τ1 & τ2) -> exp γ τ1
  proj2 :: exp γ (τ1 & τ2) -> exp γ τ2


-- Lower ----------------------------------------------
data LowerSig ty = LowerSig Type
type Lower a = (MkLType ('LowerSig a) :: LType)

class HasLower (exp :: Exp) where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ


-- Lift --------------------------------------------------

class HasLift exp lift where
  suspend :: exp Empty τ -> lift exp τ
  force   :: lift exp τ -> exp Empty τ

data Lift (exp :: Exp) (τ :: LType) = Suspend (exp Empty τ)

instance HasLift exp Lift where
  suspend = Suspend
  force (Suspend e) = e

-- Families of linear languages --------------------------

type HasBang exp = (HasLower exp)
type HasILL exp = (HasLolli exp, HasBang exp)
type HasMILL exp = (HasILL exp, HasOne exp, HasTensor exp)
type HasMELL exp = (HasMILL exp, HasLower exp)
type HasMALL exp = (HasMILL exp, HasWith exp, HasPlus exp)

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

id :: HasILL exp => Lift exp (σ ⊸ σ)
id = suspend . λ $ \x -> x

sApp :: HasILL exp => Lift exp (σ ⊸ τ) -> Lift exp σ -> Lift exp τ
sApp f e = suspend $ force  f ^ force e

uncurryL :: HasMILL exp => Lift exp ((σ1 ⊸ σ2 ⊸ τ) ⊸ σ1 ⊗ σ2 ⊸ τ)
uncurryL = suspend . λ $ \f -> λ $ \x -> 
    x `letPair` \(x1,x2) -> 
    f ^ x1 ^ x2
uncurry :: (HasMILL exp, WFCtx γ) => exp γ (σ1 ⊸ σ2 ⊸ τ) -> exp γ (σ1 ⊗ σ2 ⊸ τ)
uncurry e = force uncurryL ^ e


composeL :: HasMILL exp
         => Lift exp ((τ ⊸ ρ) ⊸ (σ ⊸ τ) ⊸ (σ ⊸ ρ))
composeL = suspend . λ $ \g -> λ $ \f -> λ $ \x -> g ^ (f ^ x)
compose :: (HasMILL exp, CMerge γ1 γ2 γ)
        => exp γ1 (τ ⊸ ρ) -> exp γ2 (σ ⊸ τ) -> exp γ (σ ⊸ ρ)
compose g f = force composeL ^ g ^ f

--------------------------------------------------------------
-- LMonad ----------------------------------------------------
--------------------------------------------------------------

class LFunctor exp (f :: LType ~> LType) where
  (<$$>) :: CMerge γ1 γ2 γ 
         => exp γ1 (σ ⊸ τ) -> exp γ2 (f @@ σ) -> exp γ (f @@ τ)
class LFunctor exp f => LApplicative exp f where
  lpure  :: WFCtx γ => exp γ τ -> exp γ (f @@ τ)
  (<**>) :: CMerge γ1 γ2 γ
         => exp γ1 (f @@ (σ ⊸ τ)) -> exp γ2 (f @@ σ) -> exp γ (f @@ τ)
class LApplicative exp m => LMonad exp m where
  (=>>=) :: CMerge γ1 γ2 γ
         => exp γ1 (m @@ σ) -> exp γ2 (σ ⊸ m @@ τ) -> exp γ (m @@ τ)


-- State monad
data LState' :: LType -> LType ~> LType
type family (f :: k1 ~> k2) @@ (x :: k1) = (r :: b) | r -> f x

type instance (LState' σ) @@ τ = σ ⊸ σ ⊗ τ
type LState σ τ = LState' σ @@ τ

instance HasMILL exp => LFunctor exp (LState' ρ) where
  f <$$> e = force lfmap ^ f ^ e
    where
      lfmap :: Lift exp ((σ ⊸ τ) ⊸ LState ρ σ ⊸ LState ρ τ)
      lfmap = suspend . λ $ \f -> λ $ \x -> λ $ \r ->
        x ^ r `letPair` \(r,s) -> r ⊗ (f ^ s)
instance HasMILL exp => LApplicative exp (LState' ρ) where
  lpure e = force lpure' ^ e
    where
      lpure' :: Lift exp (σ ⊸ LState ρ σ)
      lpure' = suspend . λ $ \x -> λ $ \r -> r ⊗ x
  f <**> e = force lapp ^ e ^ f
    where
      lapp :: Lift exp (LState ρ σ ⊸ LState ρ (σ ⊸ τ) ⊸ LState ρ τ)
      lapp = suspend . λ $ \st -> λ $ \stF -> λ $ \r ->
        st ^ r `letPair` \(r,s) ->
        stF ^ r `letPair` \(r,f) ->
        r ⊗ (f ^ s)
instance HasMILL exp => LMonad exp (LState' ρ) where
  e =>>= f = force lbind ^ e ^ f
    where
      lbind :: Lift exp (LState ρ σ ⊸ (σ ⊸ LState ρ τ) ⊸ LState ρ τ)
      lbind = suspend . λ $ \st -> λ $ \f -> λ $ \ r ->
                st ^ r `letPair` \(r,s) -> f ^ s ^ r

runLStateT :: HasMILL exp 
           => LinT exp (LState' σ) a -> Lift exp σ -> Lift exp (σ ⊗ Lower a)
runLStateT st s = suspend $ forceT st ^ force s

execLStateT :: HasMILL exp
            => LinT exp (LState' σ) a -> Lift exp σ -> Lift exp σ
execLStateT st s = suspend $ force (runLStateT st s) `letPair` \(s,a) -> 
                             a >! \_ -> s

evalLStateT :: HasMILL exp
            => LinT exp (LState' σ) a -> Lift exp σ 
            -> Lift exp (σ ⊸ One) -> Lin exp a
evalLStateT st s free = suspendL $ force (runLStateT st s) `letPair` \(s,a) ->
                                   force free ^ s `letUnit` a


---------------------------------------------------------------
-- Linearity Monad --------------------------------------------
---------------------------------------------------------------

newtype Lin exp a = Lin (Lift exp (Lower a))


suspendL :: exp Empty (Lower a) -> Lin exp a
suspendL = Lin . suspend

forceL :: Lin exp a -> exp Empty (Lower a)
forceL (Lin x) = force x

instance (HasLower exp) => Functor (Lin exp) where
  fmap f e = suspendL $ forceL e >! (put . f)
instance (HasLower exp) => Applicative (Lin exp) where
  pure = suspendL . put
  f <*> e = suspendL $ forceL e >! \a ->
                       forceL f >! \g ->
                       put $ g a
instance (HasLower exp) => Monad (Lin exp) where
  e >>= f = suspendL $ forceL e >! \a ->
                       forceL (f a)

---------------------------------------------------------------
-- Linearity Monad Transformer --------------------------------
---------------------------------------------------------------

newtype LinT exp (f :: LType ~> LType) a = LinT (Lift exp (f @@ (Lower a)))

suspendT :: exp Empty (f @@ (Lower a)) -> LinT exp f a
suspendT = LinT . suspend

forceT :: forall f exp a. LinT exp f a -> exp Empty (f @@ (Lower a))
forceT (LinT e) = force e

lowerT :: HasILL exp => (a -> b) -> exp Empty (Lower a ⊸ Lower b)
lowerT f = λ $ \x -> x >! \a -> put $ f a

lowerT2 :: HasILL exp => (a -> b -> c) -> exp Empty (Lower a ⊸ Lower b ⊸ Lower c)
lowerT2 f = λ $ \x -> x >! \a ->
            λ $ \y -> y >! \b -> put $ f a b

instance (HasILL exp, LFunctor exp f) => Functor (LinT exp f) where
    fmap g x = suspendT $ lowerT g <$$> forceT x
instance (HasILL exp, LApplicative exp f) => Applicative (LinT exp f) where
    pure a = suspendT $ lpure (put a)

    -- forceT f :: f (Lower (a -> b))
    -- forceT x :: f (Lower a) 
    -- lowerT' <$$> forceT f :: f (Lower a ⊸ Lower b)
    (<*>) :: LinT exp f (a -> b) -> LinT exp f a -> LinT exp f b
    f <*> x = suspendT $ (lowerT' <$$> forceT f) <**> forceT x
      where
        lowerT' :: exp Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
        lowerT' = λ $ \f -> f >! lowerT
instance (HasILL exp, LMonad exp f) => Monad (LinT exp f) where
    x >>= f = suspendT $ forceT x =>>= (λ $ \y -> y >! (forceT . f))

---------------------------------------------------------------
-- Patterns ---------------------------------------------------
---------------------------------------------------------------

class HasVar (exp :: Exp) where
  var :: forall x (σ :: LType) (γ :: Ctx). 
         CSingletonCtx x σ γ => exp γ σ


--type family PatMatch exp γ (σ :: LType) where
--  PatMatch exp γ σ = Var exp (Fresh γ) σ -> exp (Add


type family Tuple exp γ (σs :: [LType]) :: Type where
  Tuple exp γ '[]  = ()
  Tuple exp γ '[σ] = Pat exp γ σ
  Tuple exp γ (σ ': σs) = (Var exp (Fresh γ) σ, Tuple exp (Add (Fresh γ) σ γ) σs)

data Pat exp γ σ where
  U    :: Pat exp Empty One
--  X    :: exp γ σ -> Pat exp γ σ
  Put  :: a -> Pat exp γ (Lower a)
  Pair :: CMerge γ1 γ2 γ => Pat exp γ1 σ1 -> Pat exp γ2 σ2 -> Pat exp γ (σ1 ⊗ σ2)
  Inl  :: Pat exp γ σ1 -> Pat exp γ (σ1 ⊕ σ2)
  Inr  :: Pat exp γ σ2 -> Pat exp γ (σ1 ⊕ σ2)
data Match exp γ σ τ where
  Match :: CMerge γ1 γ2 γ => (Pat exp γ2 σ -> exp γ τ) -> Match exp γ1 σ τ

class Matchable exp σ where 
  λcase :: Match exp γ σ τ -> exp γ (σ ⊸ τ)

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
