module Interface where
 
import Prelude hiding ((^), uncurry)
-- import Prelim hiding (One)
import Types
import Classes

import Data.Kind
import qualified Data.Singletons as Sing
import Data.Singletons (Proxy)
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Num
import Data.Constraint (Dict(..))
import Debug.Trace (trace)

type (~>) a b = Sing.TyFun a b -> Type

type Var exp x σ = exp (SingletonF x σ) σ

--------------------------------------------------

--------------------------------------------------

class Eval (exp :: Sig) where
  eval     :: Monad (Effect exp) => exp γ τ -> ECtx exp γ -> Effect exp (LVal exp τ)
  fromVPut :: Monad (Effect exp) => LVal exp (Lower a) -> Effect exp a


-- For each domain:

-- 1) Declare a data type
data LolliSig ty = LolliSig ty ty

-- 2) embed it into LType
type (σ :: LType) ⊸ (τ :: LType) = MkLType ('LolliSig σ τ)
infixr 0 ⊸

-- 3) Define an interface
-- Exp = Ctx -> LType -> Type
class HasLolli (exp :: Sig) where
  λ :: forall x σ γ τ.
       (WFFreshVar x σ γ)
    => (Var exp x σ -> exp (AddF x σ γ) τ) -> exp γ (σ ⊸ τ)
  (^) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (σ :: LType) (τ :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ) -> exp γ2 σ -> exp γ τ


letin :: ( HasLolli exp, WFFreshVar x σ γ2, CMerge γ1 γ2 γ)
      => exp γ1 σ -> (Var exp x σ -> exp (AddF x σ γ2) τ) -> exp γ τ
letin e f = λ f ^ e

-- One -----------------------------------------------
data OneSig ty = OneSig
type One = (MkLType 'OneSig :: LType)

class HasOne exp where
  unit :: exp ('[] :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ

λunit :: (HasOne exp, HasLolli exp, WFFresh One γ)
      => (() -> exp γ τ) -> exp γ (One ⊸ τ)
λunit f = λ $ \x -> x `letUnit` f ()

-- Tensor ---------------------------------------------  


data TensorSig ty = TensorSig ty ty
type (σ1 :: LType) ⊗ (σ2 :: LType) = MkLType ('TensorSig σ1 σ2)

-- Exp = Ctx -> LType -> Type
class HasTensor exp where
  (⊗) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (τ1 :: LType) (τ2 :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 τ1 -> exp γ2 τ2 -> exp γ (τ1 ⊗ τ2)
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx)  (γ :: Ctx) 
                    (γ2'' :: Ctx).
             ( CMerge γ1 γ2 γ
             , WFVarTwo x1 σ1 x2 σ2 γ2 γ2''
             )
      => exp γ1 (σ1 ⊗ σ2)
      -> ((Var exp x1 σ1, Var exp x2 σ2) -> exp γ2'' τ)
      -> exp γ τ

λpair :: ( HasTensor exp, HasLolli exp
         , WFVarTwo x1 σ1 x2 σ2 γ γ''
         , WFVar x1 (σ1 ⊗ σ2) γ, WFVar x2 (σ1 ⊗ σ2) γ
         )
        => ((Var exp x1 σ1, Var exp x2 σ2) -> exp γ'' τ) -> exp γ (σ1⊗σ2 ⊸ τ)
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
  caseof :: ( WFVar x σ1 γ2, WFVar x σ2 γ2
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => exp γ1 (σ1 ⊕ σ2)
        -> (Var exp x σ1 -> exp (AddF x σ1 γ2) τ)
        -> (Var exp x σ2 -> exp (AddF x σ2 γ2) τ)
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
  put  :: a -> exp '[] (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ

λbang :: ( HasLower exp, HasLolli exp, WFFresh (Lower a) γ)
   => (a -> exp γ τ) -> exp γ (Lower a ⊸ τ)
λbang f = λ $ (>! f)

-- Lift --------------------------------------------------

class Suspendable exp τ lift | lift -> exp τ where
  suspend :: exp '[] τ -> lift
  force   :: lift -> exp '[] τ

newtype Lift (exp :: Sig) (τ :: LType) = Suspend (exp '[] τ)

instance Suspendable exp τ (Lift exp τ) where
  suspend = Suspend
  force (Suspend e) = e


-- Dependent functions ---------------------------------
-- I think this is going to be too hard to work with in haskell
type family (n :: Nat) ⨂ (σ :: LType) where
  0 ⨂ σ = One
  n ⨂ σ = σ ⊗ ((Subtract n 1) ⨂ σ)

data PiSig ty where
  PiSig :: forall α ty. (α → ty) -> PiSig ty
type Pi f = (MkLType ('PiSig f) :: LType)

class HasPi exp where
  pλ :: (forall a. Sing a → exp γ (f a)) → exp γ (Pi f)
  pApp :: exp γ (Pi f) -> Sing a -> exp γ (f a)

--instance Suspendable exp Lin (Lower α) where

-- Families of linear languages --------------------------

type HasBang exp = (HasLower exp)
type HasILL  exp = (HasLolli exp, HasBang exp)
type HasMILL exp = (HasILL exp, HasOne exp, HasTensor exp)
type HasMALL exp = (HasMILL exp, HasWith exp, HasPlus exp)

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

idL :: HasILL exp => Lift exp (σ ⊸ σ)
idL = suspend . λ $ \x -> x

sApp :: HasILL exp => Lift exp (σ ⊸ τ) -> Lift exp σ -> Lift exp τ
sApp f e = suspend $ force  f ^ force e



pair :: HasMILL exp => Lift exp (σ ⊸ τ ⊸ σ ⊗ τ)
pair = suspend . λ $ \x ->
                 λ $ \y ->
                 x ⊗ y


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

foo :: HasMILL exp => Lift exp (Lower α ⊸ Lower α ⊗ Lower α)
foo = suspend . λ $ \x -> -- x :: exp _ (Lower α)
                x >! \a -> -- a :: α
                put a ⊗ put a


--------------------------------------------------------------
-- Comonad ---------------------------------------------------
--------------------------------------------------------------

type Bang exp σ = Lower (Lift exp σ)

extract :: HasILL exp => Lift exp (Bang exp τ ⊸ τ)
extract = suspend . λbang $ \x → force x

duplicate :: HasILL exp => Lift exp (Bang exp τ ⊸ Bang exp (Bang exp τ))
duplicate = suspend . λbang $ put . suspend . put

---------------------------------------------------------------
-- Linearity Monad --------------------------------------------
---------------------------------------------------------------

newtype Lin exp a = Lin (Lift exp (Lower a))

instance Suspendable exp (Lower α) (Lin exp α) where
    suspend = Lin . suspend
    force (Lin e) = force e


--suspendL :: exp '[] (Lower a) -> Lin exp a
--suspendL = Lin . suspend

--forceL :: Lin exp a -> exp '[] (Lower a)
--forceL (Lin x) = force x

instance (HasLower exp) => Functor (Lin exp) where
  fmap f e = suspend $ force e >! (put . f)
instance (HasLower exp) => Applicative (Lin exp) where
  pure = suspend . put
  f <*> e = suspend $ force e >! \a ->
                       force f >! \g ->
                       put $ g a
instance (HasLower exp) => Monad (Lin exp) where
  e >>= f = suspend $ force e >! \a ->
                       force (f a)

run :: forall exp a. (Monad (Effect exp), Eval exp) => Lin exp a -> Effect exp a
run e = eval (force e) eEmpty >>= fromVPut

---------------------------------------------------------------
-- Linearity Monad Transformer --------------------------------
---------------------------------------------------------------

newtype LinT exp (f :: LType ~> LType) a = LinT (Lift exp (f @@ (Lower a)))

instance τ ~ (f @@ (Lower α)) => Suspendable exp τ (LinT exp f α) where
    suspend = LinT . suspend
    force (LinT x) = force x

--suspendT :: exp '[] (f @@ (Lower a)) -> LinT exp f a
--suspendT = LinT . suspend

--forceT :: forall f exp a. LinT exp f a -> exp '[] (f @@ (Lower a))
--forceT (LinT e) = force e

lowerT :: HasILL exp => (a -> b) -> exp '[] (Lower a ⊸ Lower b)
lowerT f = λ $ \x -> x >! \a -> put $ f a

lowerT2 :: HasILL exp => (a -> b -> c) 
        -> exp '[] (Lower a ⊸ Lower b ⊸ Lower c)
lowerT2 f = λ $ \x -> x >! \a ->
            λ $ \y -> y >! \b -> put $ f a b

instance (HasILL exp, LFunctor exp f) => Functor (LinT exp f) where
    fmap g x = suspend $ lowerT g <$$> force x
instance (HasILL exp, LApplicative exp f) => Applicative (LinT exp f) where
    pure a = suspend $ lpure (put a)

    -- force f :: f (Lower (a -> b))
    -- force x :: f (Lower a) 
    -- lowerT' <$$> force f :: f (Lower a ⊸ Lower b)
    (<*>) :: LinT exp f (a -> b) -> LinT exp f a -> LinT exp f b
    f <*> x = suspend $ (lowerT' <$$> force f) <**> force x
      where
        lowerT' :: exp '[] (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
        lowerT' = λ $ \f -> f >! lowerT
instance (HasILL exp, LMonad exp f) => Monad (LinT exp f) where
    x >>= f = suspend $ force x =>>= (λ $ \y -> y >! (force . f))

--------------------------------------------------------------
-- LMonad ----------------------------------------------------
--------------------------------------------------------------

class LFunctor exp (f :: LType ~> LType) where
  (<$$>) :: CMerge γ1 γ2 γ 
         => exp γ1 (σ ⊸ τ) -> exp γ2 (f @@ σ) -> exp γ (f @@ τ)
class LFunctor exp f => LApplicative exp f where
  lpure  :: exp γ τ -> exp γ (f @@ τ)
  (<**>) :: CMerge γ1 γ2 γ
         => exp γ1 (f @@ (σ ⊸ τ)) -> exp γ2 (f @@ σ) -> exp γ (f @@ τ)
class LApplicative exp m => LMonad exp m where
  (=>>=) :: CMerge γ1 γ2 γ
         => exp γ1 (m @@ σ) -> exp γ2 (σ ⊸ m @@ τ) -> exp γ (m @@ τ)

lfmapLState' :: ( HasMILL exp, CMerge γ1 γ2 γ
                , WFVarTwoFresh ρ σ γ2 γ2''
                , WFVarFreshMerge ρ γ1 γ2 γ
                )
             => exp γ2 (σ ⊸ τ) -> exp γ1 (LState ρ σ) -> exp γ (LState ρ τ)
lfmapLState' f e = λ $ \r -> e ^ r `letPair` \(r,s) -> r ⊗ (f ^ s)

lfmapLState :: forall ρ σ τ γ1 γ2 γ exp.
               ( HasMILL exp, CMerge γ1 γ2 γ)
            => exp γ2 (σ ⊸ τ) -> exp γ1 (LState ρ σ) -> exp γ (LState ρ τ)
lfmapLState = case (wfVarTwoFresh @ρ @σ @γ2, wfFreshMerge @ρ @γ1 @γ2 @γ) of 
                (Dict,Dict) -> lfmapLState'

lpureLState :: forall ρ τ γ exp. (HasMILL exp) => exp γ τ -> exp γ (LState ρ τ)
lpureLState e = case wfFresh @ρ @γ of Dict -> λ $ \r -> r ⊗ e
  -- force lpureLStateLift ^ e
  -- case wfFresh @ρ @γ of Dict -> force lpureLStateLift ^ e
  -- lpureLState' e
  -- case wfFresh @ρ @γ of Dict -> λ $ \r -> r ⊗ e

--lpureLStateLift :: HasMILL exp => Lift exp (σ ⊸ LState ρ σ)
--lpureLStateLift = suspend . λ $ \x -> λ $ \r -> r ⊗ x

-- lappLState :: (HasMILL exp, CMerge γ1 γ2 γ
--               , WFVarTwoFresh ρ σ γ2 γ2'
--               )
--            => exp γ1 (LState ρ (σ ⊸ τ)) -> exp γ2 (LState ρ σ) -> exp γ (LState ρ τ)
-- lappLState stF stE = λ $ \ρ -> stE ^ r `letPair` \(r,s) ->
--                                stF ^ r `letPair` \(r,f) ->
--                                r ⊗ (f ^ s)

lbindLState' :: ( HasMILL exp, CMerge γ1 γ2 γ
                , WFVarFreshMerge ρ γ1 γ2 γ
                , WFVarTwoFresh ρ σ γ2 γ2'
                )
             => exp γ1 (LState ρ σ) -> exp γ2 (σ ⊸ LState ρ τ) -> exp γ (LState ρ τ)
lbindLState' stE stF = λ $ \r -> stE ^ r `letPair` \(r,x) ->
                                stF ^ x ^ r 
lbindLState :: forall γ1 γ2 γ exp ρ σ τ. ( HasMILL exp, CMerge γ1 γ2 γ )
            => exp γ1 (LState ρ σ) -> exp γ2 (σ ⊸ LState ρ τ) -> exp γ (LState ρ τ)
lbindLState = case (wfFreshMerge @ρ @γ1 @γ2 @γ, wfVarTwoFresh @ρ @σ @γ2) of
                (Dict,Dict) -> lbindLState'


-- State monad

data LState' :: LType -> LType ~> LType
type family (f :: k1 ~> k2) @@ (x :: k1) = (r :: b) | r -> f x

type instance (LState' σ) @@ τ = σ ⊸ σ ⊗ τ
type LState σ τ = LState' σ @@ τ

instance HasMILL exp => LFunctor exp (LState' ρ) where
  f <$$> e = lfmapLState f e
--    where
--      lfmap :: Lift exp ((σ ⊸ τ) ⊸ LState ρ σ ⊸ LState ρ τ)
--      lfmap = suspend . λ $ \f -> λ $ \x -> λ $ \r ->
--        x ^ r `letPair` \(r,s) -> r ⊗ (f ^ s)
instance HasMILL exp => LApplicative exp (LState' ρ) where
  lpure e = lpureLState e
-- lpureLState e 
-- force lpureLStateLift ^ e
--  λ $ \r → r ⊗ e

  f <**> e = force lapp ^ e ^ f
    where
      lapp :: Lift exp (LState ρ σ ⊸ LState ρ (σ ⊸ τ) ⊸ LState ρ τ)
      lapp = suspend . λ $ \st -> λ $ \stF -> λ $ \r ->
        st ^ r `letPair` \(r,s) ->
        stF ^ r `letPair` \(r,f) ->
        r ⊗ (f ^ s)
instance HasMILL exp => LMonad exp (LState' ρ) where
  e =>>= f = lbindLState e f
--      force lbind ^ e ^ f
    where
      lbind :: Lift exp (LState ρ σ ⊸ (σ ⊸ LState ρ τ) ⊸ LState ρ τ)
      lbind = suspend . λ $ \st -> λ $ \f -> λ $ \ r ->
                st ^ r `letPair` \(r,s) -> f ^ s ^ r

lstate1 :: HasMILL exp => Lift exp (σ ⊸ σ) -> LStateT exp σ ()
lstate1 f = suspend . λ $ \s -> force f ^ s ⊗ put ()

runLStateT :: HasMILL exp 
           => LinT exp (LState' σ) a -> Lift exp σ -> Lift exp (σ ⊗ Lower a)
runLStateT st s = suspend $ force st ^ force s

execLStateT :: HasMILL exp
            => LStateT exp σ a -> Lift exp σ -> Lift exp σ
execLStateT st s = suspend $ force (runLStateT st s) `letPair` \(s,a) -> 
                             a >! \_ -> s

evalLStateT :: HasMILL exp
            => LinT exp (LState' σ) a -> Lift exp σ 
            -> Lift exp (σ ⊸ One) -> Lin exp a
evalLStateT st s free = suspend $ force (runLStateT st s) `letPair` \(s,a) ->
                                   force free ^ s `letUnit` a


-- for convenience
type LStateT exp σ α = LinT exp (LState' σ) α

class HasVar exp where
  var :: forall x (σ :: LType) (γ :: Ctx). 
         CSingletonCtx x σ γ => Proxy x -> exp γ σ

