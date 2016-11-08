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
idL = Suspend $ λ $ \x -> x



compose :: Lift ((a ⊸ b) ⊸ (b ⊸ c) ⊸ a ⊸ c)
compose = Suspend $ λ$ \f -> λ$ \g ->
            λ$ \a -> g `app` (f `app` a)


counit :: forall a. Lift (Lower (Lift a) ⊸ a)
counit = Suspend $ λ$ \ x -> x >! force

apply :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
apply = Suspend . λ$ \x -> λ$ \y -> y `app` x

-- ret :: a -> Lin a 
-- use 'run $ ret const' to get the constant out
ret a = suspendL $ force idL `app` put a


-- fmap :: (a -> b) -> Lift (Lower a ⊸ Lower b)
fmap f = Suspend . λ$ \x -> x >! \ a -> put (f a)

app2 = Suspend . λ$ \z -> λ$ \x -> λ$ \y -> 
                 z `app` x `app` y



idid = Suspend $ force idL `app` force idL

idid' = Suspend $ app (force idL) (λ $ \x -> x) 

-- We're still losing out on idid'
-- idid'' = suspend $ app (λ$ \x -> x) (λ$ \y -> y)

pairPut :: Lift (Lower String ⊗ Lower String)
pairPut = Suspend $ put "hi" ⊗ put "bye"

swapPairPut = Suspend $ force pairPut `letPair` \(x,y) -> y ⊗ x

uncurry = Suspend $ λ$ \f -> λ$ \z ->
    z `letPair` \(x,y) -> f `app` x `app` y


curry :: Lift ((a ⊗ b ⊸ c) ⊸ a ⊸ b ⊸ c)
curry = Suspend $ λ$ \f -> λ$ \x -> λ$ \y -> f `app` (x ⊗ y)


-- Plus

eitherPlus :: Either (Lift a) (Lift b) -> Lift (a ⊕ b)
eitherPlus (Left  a) = Suspend . Inl $ force a
eitherPlus (Right b) = Suspend . Inr $ force b


isoPlus1 :: Lift (a ⊗ (b ⊕ c) ⊸ (a ⊗ b) ⊕ (a ⊗ c))
isoPlus1 = Suspend . λ$ \z ->
    letPair z $ \(a,z) ->
    caseof z (\b -> Inl $ a ⊗ b)
             (\c -> Inr $ a ⊗ c)

isoPlus2 :: Lift ( (a ⊗ b) ⊕ (a ⊗ c) ⊸ a ⊗ (b ⊕ c) )
isoPlus2 = Suspend . λ$ \z ->
  caseof z case1 case2
  where
    case1 p = p `letPair` \(a,b) -> a ⊗ Inl b
    case2 p = p `letPair` \(a,c) -> a ⊗ Inr c

-- Bang

coret :: LExp 'Empty a -> LExp 'Empty (Bang a)
coret = put . Suspend

dupTensor :: Lift (Bang a ⊸ Bang a ⊗ Bang a)
dupTensor = Suspend $ λ$ \a -> 
    a >! \a' -> put a' ⊗ put a'

drop :: Lift (Bang a ⊸ One)
drop = Suspend . λ$ \a -> a >! \_ -> Unit

oneDuplicable :: Lift (One ⊸ Bang One)
oneDuplicable = Suspend . λ$ \x -> x `letUnit` coret Unit

-- lift and lower

lowerbind :: Lift (Lower a ⊸ Lower b) -> a -> Lin b
lowerbind f a = suspendL $ force f `app` put a

liftMap :: Lift (a ⊸ b) -> Lift a -> Lift b
liftMap f a = Suspend $ force f `app` force a

liftMap2 :: Lift (a ⊸ b ⊸ c) -> Lift a -> Lift b -> Lift c
liftMap2 f a b = liftMap (liftMap f a) b


-- With

dupWith :: Lift (a ⊸ a & a)
dupWith = Suspend $ λ$ \a -> Prod a a

fst :: Lift (a & b ⊸ a)
fst = Suspend . λ$ \p -> Fst p

snd :: Lift (a & b ⊸ b)
snd = Suspend . λ$ \p -> Snd p

iso1 :: Lift (Bang (a & b) ⊸ Bang a ⊗ Bang b)
iso1 = Suspend . λ$ \x ->
    x >! \p -> (coret . Fst $ force p) ⊗ (coret . Snd $ force p)

iso2 :: Lift (Bang a ⊗ Bang b ⊸ Bang (a & b))
iso2 = Suspend . λ$ \z -> 
    z `letPair` \(x,y) -> 
    x >! \a ->
    y >! \b ->
    coret $ force a & force b

