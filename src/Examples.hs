{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, PartialTypeSignatures, TemplateHaskell, LambdaCase, FlexibleContexts,
             QuasiQuotes
#-}


module Examples where

import Types
import Lang
import Context
import Proofs
import Classes
import Interface
import TH 

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Prelude hiding (abs)

type X = 'Z
type Y = 'S 'Z
type Z = 'S ('S 'Z)


-- swap :: Lift (s⊗t ⊸ t⊗s)
swap = suspend $ λ @Z 
               $ letpair @X @Y @'[] (var @Z)
               $ (var @Y) ⊗ (var @X)
-- swap' = suspend $ λ @Z
--       $ match @_ @_ @_ @_ (MkPair (MkVar @X) (MkVar @Y)) (var @Z)
--       $ var @Y ⊗ var @X
--   where 
--     p :: SPat (PPair (PVar X) (PVar Y))
--     p = MkPair (MkVar @X) (MkVar @Y)
--     f :: (CAddPat (PPair (PVar X) (PVar Y)) (s ⊗ t) g2 g2'
--          ,CMerge2 '[ 'Unused, 'Unused, 'Unused] g2 g3)
--       => LExp g2' r 
--       -> LExp '[ 'Used s, 'Used t, 'Unused]  r
--     f = p `match` var @Z

-- e1a ∷ Lift (a ⊸ a)
-- e1a = [ suspend | λ x. x ]

idL = suspend $ λ @X (var @X)


suspendT e = $(transformTH [|e|])

idNL x = x
--idTH = $(transformTH $ [| \x -> x |])
idTH = $(transformTH [| \x -> x |])
--idTH' = suspendT (\x -> x)

-- e1 = [ suspend | λ x -> x |]


--e2 :: forall a. Lift (Lower (Lift a) ⊸ a)
-- suspend $ λ x. x >! force
counit = suspend $ λ @X $ var @X >! force 

-- e3a :: Lift (a ⊸ (a ⊸ b) ⊸ b)
-- e3a = [ suspend | λ x. λ f. f x ]


--e3 :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
-- suspend $ λ x. λ y. x y
apply = suspend $ λ @X 
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

--e6 :: forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ a ⊸ b ⊸ c)
e6 = suspend $ λ @Z $ λ @X $ λ @Y 
             $ (var @Z `app` var @X) `app` var @Y

--e6bad = suspend $ λ @Z $ λ @X $ λ @Y
--                $ var @Z `app` var @X `app` var @Z
--e6bad = suspend $ λ @X $ var @X `app` var @X

idid = suspend $ force idL `app` force idL
