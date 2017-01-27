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


idL ∷ Lift sig (a ⊸ a)
idL = Suspend $ λ $ \x -> var x



compose :: Lift sig ((a ⊸ b) ⊸ (b ⊸ c) ⊸ a ⊸ c)
compose = Suspend $ λ$ \f -> λ$ \g ->
            λ$ \a -> var g `app` (var f `app` var a)


counit :: Lift sig (Lower (Lift sig a) ⊸ a)
counit = Suspend $ λ$ \ x -> var x >! force

apply :: Lift sig (a ⊸ (a ⊸ b) ⊸ b)
apply = Suspend . λ$ \x -> λ$ \y -> var y `app` var x

-- ret :: a -> Lin a 
-- use 'run $ ret const' to get the constant out
ret a = suspendL $ force idL `app` put a


-- fmap :: (a -> b) -> Lift (Lower a ⊸ Lower b)
fmap f = Suspend . λ$ \x -> var x >! \ a -> put (f a)

app2 = Suspend . λ$ \z -> λ$ \x -> λ$ \y -> 
                 var z `app` var x `app` var y



idid = Suspend $ force idL `app` force idL

idid' = Suspend $ app (force idL) (λ $ \x -> var x) 

-- We're still losing out on idid'
-- idid'' = Suspend $ λ$ \z -> 
--    app (λ$ \x -> var z `app` var x) (λ$ \y -> var y)

pairPut :: Lift sig (Lower String ⊗ Lower String)
pairPut = Suspend $ put "hi" ⊗ put "bye"

swapPairPut = Suspend $ force pairPut `letPair` \(x,y) -> var y ⊗ var x

uncurry :: Lift sig ((a ⊸ b ⊸ c) ⊸ a ⊗ b ⊸ c)
uncurry = Suspend $ λ$ \f -> λ$ \z ->
    var z `letPair` \(x,y) -> var f `app` var x `app` var y


curry :: Lift sig ((a ⊗ b ⊸ c) ⊸ a ⊸ b ⊸ c)
curry = Suspend $ λ$ \f -> λ$ \x -> λ$ \y -> var f `app` (var x ⊗ var y)


-- Plus

eitherPlus :: Either (Lift sig a) (Lift sig b) -> Lift sig (a ⊕ b)
eitherPlus (Left  a) = Suspend . Inl $ force a
eitherPlus (Right b) = Suspend . Inr $ force b


isoPlus1 :: Lift sig (a ⊗ (b ⊕ c) ⊸ (a ⊗ b) ⊕ (a ⊗ c))
isoPlus1 = Suspend . λ$ \z ->
    var z `letPair` \(a,z) ->
    caseof (var z)
      (\b -> Inl $ var a ⊗ var b)
      (\c -> Inr $ var a ⊗ var c)

isoPlus2 :: Lift sig ( (a ⊗ b) ⊕ (a ⊗ c) ⊸ a ⊗ (b ⊕ c) )
isoPlus2 = Suspend . λ$ \z ->
  caseof (var z) case1 case2
  where
    case1 p = var p `letPair` \(a,b) -> var a ⊗ Inl (var b)
    case2 p = var p `letPair` \(a,c) -> var a ⊗ Inr (var c)

-- Bang

coret :: LExp sig 'Empty a -> LExp sig 'Empty (Bang sig a)
coret = put . Suspend

dupTensor :: Lift sig (Bang sig a ⊸ Bang sig a ⊗ Bang sig a)
dupTensor = Suspend $ λ$ \x -> 
    var x >! \a -> put a ⊗ put a

drop :: Lift sig (Bang sig a ⊸ One)
drop = Suspend . λ$ \a -> var a >! \_ -> Unit

oneDuplicable :: Lift sig (One ⊸ Bang sig One)
oneDuplicable = Suspend . λ$ \x -> var x `letUnit` coret Unit

-- lift and lower

lowerbind :: Lift sig (Lower a ⊸ Lower b) -> a -> Lin sig b
lowerbind f a = suspendL $ force f `app` put a

liftMap :: Lift sig (a ⊸ b) -> Lift sig a -> Lift sig b
liftMap f a = Suspend $ force f `app` force a

liftMap2 :: Lift sig (a ⊸ b ⊸ c) -> Lift sig a -> Lift sig b -> Lift sig c
liftMap2 f a b = liftMap (liftMap f a) b


-- With

dupWith :: Lift sig (a ⊸ a & a)
dupWith = Suspend $ λ$ \a -> Prod (var a) (var a)

fst :: Lift sig (a & b ⊸ a)
fst = Suspend . λ$ \p -> Fst $ var p

snd :: Lift sig (a & b ⊸ b)
snd = Suspend . λ$ \p -> Snd $ var p

iso1 :: Lift sig (Bang sig (a & b) ⊸ Bang sig a ⊗ Bang sig b)
iso1 = Suspend . λ$ \x ->
    var x >! \p -> (coret . Fst $ force p) ⊗ (coret . Snd $ force p)

iso2 :: Lift sig (Bang sig a ⊗ Bang sig b ⊸ Bang sig (a & b))
iso2 = Suspend . λ$ \z -> 
    var z `letPair` \(x,y) -> 
    var x >! \a ->
    var y >! \b ->
    coret $ force a & force b

