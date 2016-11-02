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
-- swap = suspend $ λ @Z 
--                $ letpair @X @Y @'[] (var @Z)
--                $ (var @Y) ⊗ (var @X)
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

idL   = suspend . λ$ \x -> x

-- counit :: forall a. Lift (Lower (Lift a) ⊸ a)
-- suspend $ λ x. x >! force
counit = suspend . λ$ \x -> x >! force 

-- apply :: forall a b. Lift (a ⊸ (a ⊸ b) ⊸ b)
-- suspend $ λ x. λ y. x y
apply = suspend . λ$ \x-> λ$ \y -> y `app` x

-- fmap' :: (a -> b) -> Lift (Lower a ⊸ Lower b)
-- [ suspend | λ x → x >! λ a -> put (f a) |]
fmap' f = suspend $ λ$ \x -> x >! \ a -> put (f a)

-- e4 :: Lift (Lower Bool)
-- var @X :: LExp '[ t ] t
-- λ @X (var @X) :: CAddCtx x s g '[ t ] => LExp g (s ⊸ t)
ret a = run . suspendL $ force idL `app` put a

--app2 :: forall a b c. Lift ((a ⊸ b ⊸ c) ⊸ a ⊸ b ⊸ c)
app2 = suspend . λ$ \z -> λ$ \x -> λ$ \y -> z `app` x `app` y


idid = suspend $ force idL `app` force idL

-- case

-- swap :: Lift (Tuple [a,b] ⊸ Tuple [b,a])
-- swap = suspend . λ$ \x -> caseof' x $ \case 
--   LExpCons _ y (LExpCons _ z LExpNil) -> tup $ z .& y 

-- failing examples -----------------------------

-- bad = suspend . λ $ \z -> z `app` z
-- bad = suspend . λ $ \x -> λ $ \y -> x

--e6bad = suspend $ λ @Z $ λ @X $ λ @Y
--                $ var @Z `app` var @X `app` var @Z
--e6bad = suspend $ λ @X $ var @X `app` var @X



-- Template Haskell Examples ----------------------------

-- suspendT e = $(transformTH [|e|])
idNL x = x
--idTH = $(transformTH $ [| \x -> x |])
--idTH = $(transformTH [| \x -> x |])
--idTH' = suspendT (\x -> x)









