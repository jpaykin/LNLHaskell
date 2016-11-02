{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures, FlexibleContexts, ConstraintKinds
#-}


module Examples where

import Types
import Lang
import Context
import Interface

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)

-- idL ∷ Lift (a ⊸ a)
idL = Suspend . λ$ \x -> x


-- counit :: forall a. Lift (Lower (Lift a) ⊸ a)
counit = Suspend . λ$ \ x -> x >! force

--e3 :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
apply = Suspend . λ$ \x -> λ$ \y -> y `app` x

-- ret :: a -> Lin a 
-- use 'run $ ret const' to get the constant out
ret a = suspendL $ force idL `app` put a


-- fmap :: (a -> b) -> Lift (Lower a ⊸ Lower b)
fmap f = suspend . λ$ \x -> x >! \ a -> put (f a)

-- forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ a ⊸ b ⊸ c)
app2 = Suspend . λ$ \z -> λ$ \x -> λ$ \y -> 
             z `app` x `app` y

idid = suspend $ force idL `app` force idL

-- idid' = Suspend $ (λ $ \x -> x) `app` force idL

pairPut :: Lift (Lower String ⊗ Lower String)
pairPut = suspend $ put "hi" ⊗ put "bye"

swapPairPut = suspend @'[ 'Unused, 'Unused ] $ 
                force pairPut `letPair` \ (x,y) -> x ⊗ y

-- uncurry :: Lift ((a ⊸ b ⊸ c) ⊸ (a ⊗ b ⊸ c))
-- uncurry = Suspend . λ$ \f -> λ$ \z ->
--             letPair z $ \(x,y) -> f `app` x `app` y

-- curry :: Lift ((a ⊗ b ⊸ c) ⊸ a ⊸ b ⊸ c)
curry = Suspend $ λ$ \f -> λ$ \x -> λ$ \y -> f `app` (x ⊗ y)
