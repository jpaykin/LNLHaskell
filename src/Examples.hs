{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures
#-}


module Examples where

import Types
import Lang
import Interface

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)

-- idL ∷ Lift (a ⊸ a)
idL = suspend $ λ @X (var @X)


-- counit :: forall a. Lift (Lower (Lift a) ⊸ a)
counit = suspend $ λ @X $ var @X >! force 

--e3 :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
apply = suspend $ λ @X 
                $ λ @Y 
                $    var @Y 
               `app` var @X 

-- ret :: a -> Lin a 
-- use 'run $ ret const' to get the constant out
ret a = suspendL $ force idL `app` put a


-- fmap :: (a -> b) -> Lift (Lower a ⊸ Lower b)
fmap f = suspend $ λ @X $ var @X >! \ a -> put (f a)

-- forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ a ⊸ b ⊸ c)
app2 = suspend $ λ @Z $ λ @X $ λ @Y 
             $ (var @Z `app` var @X) `app` var @Y

idid = suspend $ force idL `app` force idL
