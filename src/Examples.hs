{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures
#-}


module Examples where

import Types
import Interface



e1 :: forall a. Lift '[ X ] (a ⊸ a)
e1 = suspend $ λ @X @'[] $ var @X @'[]

e2 :: forall a. Lift '[ X ] (Lower (Lift '[ X ] a) ⊸ a)
-- suspend $ λ x. x >! force
e2 = suspend $ λ @X @'[] 
             $ var @X @'[]  >! force 

e3 :: forall a b. Lift '[ X, Y ] (a ⊸ ((a ⊸ b) ⊸ b))
-- suspend $ λ x. λ y. x y
e3 = suspend $ λ @X @'[]
             $ λ @Y @'[ X ] 
             $    var @Y @'[ X ] 
               @@ var @X @'[]

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)
