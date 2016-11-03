{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures, FlexibleContexts, ConstraintKinds
#-}


module Examples where

import Prelude hiding (fst, snd)
import Types
import Lang
import Context
import Interface
import Data.Constraint -- Dict

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)

idL ∷ forall a. Lift (a ⊸ a)
idL = Suspend $ λ$ \x -> x


counit :: forall a. Lift (Lower (Lift a) ⊸ a)
counit = Suspend $ λ$ \ x -> x >! force

apply :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
apply = Suspend . λ$ \x -> λ$ \y -> y `app` x

-- ret :: a -> Lin a 
-- use 'run $ ret const' to get the constant out
ret a = suspendL $ force idL `app` put a


-- fmap :: (a -> b) -> Lift (Lower a ⊸ Lower b)
-- Note, fmap actually leaves the ctx unspecified?
fmap f = suspend . λ$ \x -> x >! \ a -> put (f a)

-- forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ a ⊸ b ⊸ c)
app2 = Suspend . λ$ \z -> λ$ \x -> λ$ \y -> 
             z `app` x `app` y

idid = suspend $ force idL `app` force idL

idid' = Suspend $ app @_ @'[] (force idL) (λ $ \x -> x) 

pairPut :: Lift (Lower String ⊗ Lower String)
pairPut = suspend $ put "hi" ⊗ put "bye"

swapPairPut = suspend @'[ 'Unused, 'Unused ] $ 
                force pairPut `letPair` \ (x,y) -> y ⊗ x


uncurry :: forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ (a ⊗ b ⊸ c))
uncurry = suspend @'[ 'Unused, 'Unused, 'Unused, 'Unused ] $ λ$ \f -> λ$ \z -> 
    z `letPair` \ (x,y) -> f `app` x `app` y


curry :: Lift ((a ⊗ b ⊸ c) ⊸ a ⊸ b ⊸ c)
curry = Suspend $ λ$ \f -> λ$ \x -> λ$ \y -> f `app` (x ⊗ y)

dupTensor :: Lift (Bang a ⊸ Bang a ⊗ Bang a)
dupTensor = Suspend $ λ$ \a -> 
    a >! \a' -> put a' ⊗ put a'

-- Bang

coret :: LExp '[] a -> LExp '[] (Bang a)
coret = put . Suspend

-- With

liftMap :: Lift (a ⊸ b) -> Lift a -> Lift b
liftMap f a = Suspend $ force f `app` force a

liftMap2 :: Lift (a ⊸ b ⊸ c) -> Lift a -> Lift b -> Lift c
liftMap2 f a b = liftMap (liftMap f a) b

dupWith :: Lift (a ⊸ a & a)
dupWith = Suspend $ λ$ \a -> Prod a a

fst :: Lift (a & b ⊸ a)
fst = Suspend . λ$ \p -> Fst p

snd :: Lift (a & b ⊸ b)
snd = Suspend . λ$ \p -> Snd p


iso1 :: Lift (Bang (a & b) ⊸ Bang a ⊗ Bang b)
iso1 = Suspend . λ$ \x ->
     x >! \p -> 
    (coret . Fst $ force p) ⊗ (coret . Snd $ force p)

iso2 :: Lift (Bang a ⊗ Bang b ⊸ Bang (a & b))
iso2 = suspend @'[ 'Unused, 'Unused, 'Unused ] . λ$ \z ->
    z `letPair` \(x,y) ->
    x >! \a ->
    y >! \b ->
    coret $ force a & force b
