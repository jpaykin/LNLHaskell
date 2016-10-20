{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures
#-}


module Test where

import Types
import Interface

e1 :: forall a. Lift '[ 'Z ] (a ⊸ a)
e1 = suspend @'[ 'Z ] $ λ @'Z @a @'[] @'[] (var @'Z @a @'[] @'[])

e2 :: forall a. Lift '[ 'Z ] (Lower (Lift '[ 'Z ] a) ⊸ a)
-- suspend $ λ x. x >! force
e2 = suspend @'[ 'Z ] $ λ @'Z @_ @'[] @'[] 
                      $ var @'Z @_ @'[] @'[] >! force @'[ 'Z ]

e3 :: forall a b. Lift '[ 'Z, 'S 'Z] (a ⊸ ((a ⊸ b) ⊸ b))
-- suspend $ λ x. λ y. x y
e3 = suspend @'[ 'Z, 'S 'Z ] $ λ @'Z @a @'[] @'[ 'S 'Z ]
                             $ λ @('S 'Z) @(a ⊸ b) @'[ 'Z ] @'[]
                             $ var @('S 'Z) @(a ⊸ b) @'[ 'Z ] @'[]
                            @@ var @'Z @a @'[] @'[ 'S 'Z ]
