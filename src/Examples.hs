{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures, TemplateHaskell
#-}


module Examples where

import Types
import Lang
import Interface
import TH 

import Language.Haskell.TH
import Prelude hiding (abs)

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)


e0 :: forall a. LExp '[] (a ⊸ a)
e0 = λ @X (var @X)

e0' :: forall a. LExp '[ 'Used a ] a
e0' = var @X


-- e1a ∷ Lift (a ⊸ a)
-- e1a = [ suspend | λ x. x ]


--e1 :: forall a. Lift (a ⊸ a)
idL = suspend $ λ @X (var @X)


suspendT e = $(transformTH [|e|])

idNL x = x
idTH = $(transformTH $ [| \x -> x |])
--idTH' = suspendT (\x -> x)

-- e1 = [ suspend | λ x -> x |]


--e2 :: forall a. Lift (Lower (Lift a) ⊸ a)
-- suspend $ λ x. x >! force
e2 = suspend $ λ @X
             $ var @X >! force 

-- e3a :: Lift (a ⊸ (a ⊸ b) ⊸ b)
-- e3a = [ suspend | λ x. λ f. f x ]


--e3 :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
-- suspend $ λ x. λ y. x y
e3 = suspend $ λ @X 
             $ λ @Y 
             $    var @Y 
               `app` var @X 

-- e4 :: Lift (Lower Bool)
-- var @X :: LExp '[ t ] t
-- λ @X (var @X) :: CAddCtx x s g '[ t ] => LExp g (s ⊸ t)
e4 = run . suspendL $ force idL `app` put "Hi"

-- e5 :: (a -> b) -> Lift (Lower a ⊸ Lower b)
e5 f = suspend $ λ @X $ var @X >! \ a -> put (f a)
-- e5 f = [ suspend | λ x → x >! λ a -> put (f a) |]



idid = suspend $ force idL `app` force idL
