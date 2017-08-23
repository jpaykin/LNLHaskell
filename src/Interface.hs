{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             InstanceSigs, TypeApplications, 
             ScopedTypeVariables, UndecidableInstances,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             TypeFamilyDependencies, LambdaCase
#-}

module Interface where
 
import Prelude hiding ((^), uncurry, take, read, One)
import Control.Monad (forM_)
import Types
import Classes

import Data.Kind
import qualified Data.Singletons as Sing
type (~>) a b = Sing.TyFun a b -> Type




class HasLolli (exp :: Ctx -> LType -> Type) where
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

class HasOne exp where
  unit :: exp (Empty :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ

λunit :: (HasOne exp, HasLolli exp, WFFresh One γ)
      => (() -> exp γ τ) -> exp γ (One ⊸ τ)
λunit f = λ $ \x -> x `letUnit` f ()

-- Tensor ---------------------------------------------  

type Var exp x σ = exp (SingletonF x σ) σ

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

λpair :: (HasTensor exp, HasLolli exp
         , CSingletonCtx x1 σ1 γ1, CSingletonCtx x2 σ2 γ2
         , CAddCtx x1 σ1 γ γ', CAddCtx x2 σ2 γ' γ''
         , x1 ~ Fresh γ, x2 ~ Fresh γ'
         , WFVar x1 (σ1 ⊗ σ2) γ, WFVar x2 (σ1 ⊗ σ2) γ
         )
        => ((exp γ1 σ1, exp γ2 σ2) -> exp γ'' τ) -> exp γ (σ1⊗σ2 ⊸ τ)
λpair f = λ $ \z -> z `letPair` f



-- Lower ----------------------------------------------
class HasLower exp where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ

λbang :: ( HasLower exp, HasLolli exp, WFFresh (Lower a) γ)
   => (a -> exp γ τ) -> exp γ (Lower a ⊸ τ)
λbang f = λ $ (>! f)

-- Lift --------------------------------------------------

class HasLift exp τ lift | lift -> exp τ where
  suspend :: exp Empty τ -> lift
  force   :: lift -> exp Empty τ

data Lift exp (τ :: LType) = Suspend (exp Empty τ)

instance HasLift exp τ (Lift exp τ) where
  suspend = Suspend
  force (Suspend e) = e

-- File Handles ------------------------------------------

class HasMILL exp => HasFH exp where
  open :: String -> exp Empty Handle
  read :: exp γ Handle -> exp γ (Handle ⊗ Lower Char)
  write :: exp γ Handle -> Char -> exp γ Handle
  close :: exp γ Handle -> exp γ One

-- Families of linear languages --------------------------

type HasBang exp = (HasLower exp)
type HasILL exp = (HasLolli exp, HasBang exp)
type HasMILL exp = (HasILL exp, HasOne exp, HasTensor exp)

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

idL :: HasILL exp => Lift exp (σ ⊸ σ)
idL = suspend . λ $ \x -> x

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


-- File handle examples --


writeString :: HasFH exp => String -> exp γ Handle -> exp γ Handle
writeString s e = foldl write e s

readWriteTwice :: HasFH exp => exp Empty (Handle ⊸ Handle)
readWriteTwice = λ $ \h -> read h `letPair` \(h,x) ->
                           x >! \c ->
                           writeString [c,c] h

withFile :: HasFH exp => String -> Lift exp (Handle ⊸ Handle ⊗ Lower a) -> Lin exp a
withFile name f = suspend $ force f ^ open name `letPair` \(h,a) -> 
                            close h `letUnit` a

readM :: HasFH exp => exp Empty (LState Handle (Lower Char))
readM = λ read

writeM :: HasFH exp => Char -> exp Empty (LState Handle One)
writeM c = λ $ \h -> write h c ⊗ unit

readWriteTwiceM :: HasFH exp => Lift exp (LState Handle One)
readWriteTwiceM = suspend $ readM    =>>= (λbang $ \c ->
                            writeM c =>>= (λunit $ \() -> writeM c))

readT :: HasFH exp => LStateT exp Handle Char
readT = suspend readM

writeT :: HasFH exp => Char -> LStateT exp Handle ()
writeT c = suspend $ writeM c =>>= (λunit $ \() -> lpure $ put ())

readWriteTwiceT :: HasFH exp => LStateT exp Handle ()
readWriteTwiceT = do c <- readT
                     writeT c
                     writeT c

take :: HasFH exp => Int -> LStateT exp Handle String
take n | n <= 0    = return ""
take n | otherwise = do c <- readT
                        s <- take (n-1)
                        return $ c:s

writeStringT :: HasFH exp => String -> LStateT exp Handle ()
writeStringT s = forM_ s writeT

withFileT :: HasFH exp => String -> LStateT exp Handle a -> Lin exp a
withFileT name st = evalLStateT st (suspend $ open name) (suspend $ λ close)

--test :: Lin Shallow String
--test = do withFileT "foo" $ writeStringT "Hello world!"
--          withFileT "foo" $ take 7





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

instance HasLift exp (Lower α) (Lin exp α) where
    suspend = Lin . suspend
    force (Lin e) = force e


--suspendL :: exp Empty (Lower a) -> Lin exp a
--suspendL = Lin . suspend

--forceL :: Lin exp a -> exp Empty (Lower a)
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

class Eval exp where
  eval :: exp γ τ -> ECtx γ -> IO (LVal τ)

run :: forall exp a. Eval exp => Lin exp a -> IO a
run e = fromVPut <$> eval (force e) eEmpty

---------------------------------------------------------------
-- Linearity Monad Transformer --------------------------------
---------------------------------------------------------------

newtype LinT exp (f :: LType ~> LType) a = LinT (Lift exp (f @@ (Lower a)))

instance τ ~ (f @@ (Lower α)) => HasLift exp τ (LinT exp f α) where
    suspend = LinT . suspend
    force (LinT x) = force x

--suspendT :: exp Empty (f @@ (Lower a)) -> LinT exp f a
--suspendT = LinT . suspend

--forceT :: forall f exp a. LinT exp f a -> exp Empty (f @@ (Lower a))
--forceT (LinT e) = force e

lowerT :: HasILL exp => (a -> b) -> exp Empty (Lower a ⊸ Lower b)
lowerT f = λ $ \x -> x >! \a -> put $ f a

lowerT2 :: HasILL exp => (a -> b -> c) 
        -> exp Empty (Lower a ⊸ Lower b ⊸ Lower c)
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
        lowerT' :: exp Empty (Lower (a -> b) ⊸ Lower a ⊸ Lower b)
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
         CSingletonCtx x σ γ => Sing x -> exp γ σ

-- non-examples
--discard :: HasMILL exp => Lift exp (σ ⊸ One)
--discard = suspend . λ $ \_ → unit

--dup :: HasMILL exp => Lift exp (σ ⊸ σ ⊗ σ)
--dup = suspend . λ $ \x → x ⊗ x
