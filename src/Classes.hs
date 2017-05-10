{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             InstanceSigs, TypeApplications, ScopedTypeVariables, RankNTypes,
             EmptyCase, FlexibleContexts, UndecidableInstances,
             ConstraintKinds, PartialTypeSignatures
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors 
                               -fno-warn-redundant-constraints #-}

module Classes where

import Prelude hiding (div)
import Data.Singletons
import Data.Constraint
import Data.Type.Equality
import Unsafe.Coerce

import Prelim
--import Context
import Types
--import Proofs

-- In Context ---------------------------------------------

class CIn  (x :: Nat) (σ :: LType) (g :: Ctx)
class CInN (x :: Nat) (σ :: LType) (g :: NCtx)

instance CInN 'Z σ ('End σ)
instance CInN 'Z σ ('Cons ('Just σ) g)
instance (CInN x σ g) => CInN ('S x) σ ('Cons u g)

instance CInN x σ g => CIn x σ ('N g)
  

-- Add To Context ----------------------------------------------

class (γ' ~ AddF x σ γ, γ ~ Remove x γ', Lookup γ' x ~ Just σ)
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 
    | x σ γ -> γ', x γ' -> σ γ
  where
    addLookupNEq :: (x == y) ~ False 
                 => Sing x -> Sing y -> Dict (Lookup γ' y ~ Lookup γ y)

instance (CAddCtxN x σ γ γ' (CountNMinus1 γ')) => 
         CAddCtx x σ γ (N γ')
  where
--    addLookupNEq _ = addLookupNNEq @x @σ @γ @γ'
    addLookupNEq _ = unsafeCoerce (Dict :: Dict ())

class ( γ' ~ AddNNF x σ γ, N γ ~ RemoveN x γ'
      , len ~ CountNMinus1 γ', LookupN γ' x ~ Just σ)
    => CAddNCtxN (x :: Nat) (σ :: LType) (γ :: NCtx) (γ' :: NCtx) (len :: Nat)
    | x σ γ -> γ' len, x γ' len -> σ γ
--  where
--    addLookupNNNEq :: (x == y) ~ False 
--                   => Sing y -> Dict (LookupN γ' y ~ LookupN γ y)

instance (CountNMinus1 γ ~ len, WFNCtx γ)
      => CAddNCtxN Z σ (Cons Nothing γ) (Cons (Just σ) γ) (S len)
--  where
--    addLookupNNNEq (SS _) = Dict
instance (CSingletonNCtx x σ γ', WFNCtx γ')
      => CAddNCtxN (S x) σ (End τ) (Cons (Just τ) γ') (S Z)
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = singLookupNNEq @x @σ y
instance CAddNCtxN x (σ :: LType) (γ :: NCtx) (γ' :: NCtx) (S n)
      => CAddNCtxN (S x) σ (Cons Nothing γ) (Cons Nothing γ') (S n)
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = addLookupNNNEq @x @σ @γ y
instance CAddNCtxN x (σ :: LType) (γ :: NCtx) (γ' :: NCtx) (S n)
      => CAddNCtxN (S x) σ (Cons (Just τ) γ) (Cons (Just τ) γ') (S (S n))
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = addLookupNNNEq @x @σ @γ y

class ( γ' ~ AddNF x σ γ, γ ~ RemoveN x γ'
      , len ~ CountNMinus1 γ' -- ~ Count γ
      , LookupN γ' x ~ Just σ)
   => CAddCtxN (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: NCtx) (len :: Nat)
    | x σ γ -> len γ', x γ' len -> σ γ 
--  where
--    addLookupNNEq :: (x == y) ~ False 
--                  => Sing y -> Dict (LookupN γ' y ~ Lookup γ y)

instance CAddNCtxN x σ γ γ' (S len) => CAddCtxN x σ (N γ) γ' (S len)
--  where
--    addLookupNNEq = addLookupNNNEq @x @σ @γ
instance CSingletonNCtx x σ γ'  => CAddCtxN x σ Empty γ' Z
--  where
--    addLookupNNEq = singLookupNEq @x @σ


add :: forall σ γ γ' x sig. CAddCtx x σ γ γ' 
    => Sing x -> LVal sig σ -> ECtx sig γ -> ECtx sig γ'
add x v (ECtx f) = ECtx $ \Dict y -> case eqSNat x y of
  Left  Dict -> v
  Right Dict -> case addLookupNEq @x @σ @γ @γ' x y of Dict -> f Dict y

---------------------

-- outputs the number of variables used in the NCtx
-- since every NCtx has size >= 1, we first compute |g|-1 and then add one.
type family CountNMinus1 γ :: Nat where
  CountNMinus1 ('End _) = 'Z
  CountNMinus1 ('Cons ('Just _) γ) = 'S (CountNMinus1 γ)
  CountNMinus1 ('Cons 'Nothing γ)  = CountNMinus1 γ
type CountN γ = S (CountNMinus1 γ)

type family IsSingletonF  g :: Bool where
  IsSingletonF ('End σ)            = 'True
  IsSingletonF ('Cons ('Just _) _) = 'False
  IsSingletonF ('Cons 'Nothing   g) = IsSingletonF g

type family IsDouble g :: Bool where
  IsDouble ('End σ) = 'False
  IsDouble ('Cons ('Just _) g) = IsSingletonF g
  IsDouble ('Cons 'Nothing g)   = IsDouble g

class CIsSingleton (g :: NCtx) (flag :: Bool) | g -> flag where

instance CIsSingleton ('End σ) 'True where
instance CIsSingleton ('Cons ('Just σ) g) 'False where
instance CIsSingleton g b => CIsSingleton ('Cons 'Nothing g) b where

-- Singleton Context ------------------------------------------

type WFVar x σ γ = ( CSingletonCtx x σ (SingletonF x σ)
                   , CAddCtx x σ γ (AddF x σ γ) 
                   , CMerge γ (SingletonF x σ) (AddF x σ γ)
                   , WFCtx γ
                   )
class WFVar (Fresh γ) σ γ => WFFresh σ γ
class WFVar (FreshN γ) σ (N γ) => WFNFresh σ γ

instance WFFresh σ Empty
instance WFNFresh σ γ => WFFresh σ (N γ)
instance WFNFresh σ (End τ)
instance WFNCtx γ => WFNFresh σ (Cons Nothing γ)
--instance WFNFresh σ γ => WFNFresh σ (Cons (Just τ) γ)
-- TODO

class (g ~ SingletonF x σ, Remove x g ~ Empty, Lookup g x ~ Just σ, SingI x)
   => CSingletonCtx (x :: Nat) (σ :: LType) (g :: Ctx) 
      | x σ -> g, g -> x σ where
  singLookupNEq :: forall y.  (x == y) ~ False 
                => Sing y -> Dict (Lookup g y ~ Nothing)
class (g ~ SingletonNF x σ, RemoveN x g ~ Empty, CountNMinus1 g ~ Z
      , LookupN g x ~ Just σ, SingI x)
   => CSingletonNCtx (x :: Nat) (σ :: LType) (g :: NCtx) 
    | x σ -> g, g -> x σ where
--  singLookupNNEq :: forall y. (x == y) ~ False 
--                 => Sing y -> Dict (LookupN g y ~ Nothing)

instance CSingletonNCtx 'Z σ ('End σ) where
--  singLookupNNEq (SS _) = Dict
instance CSingletonNCtx x σ g => CSingletonNCtx ('S x) σ ('Cons 'Nothing g) where
--  singLookupNNEq SZ = Dict
--  singLookupNNEq (SS y) = singLookupNNEq @x @σ y
instance CSingletonNCtx x σ g => CSingletonCtx x σ ('N g) where
--  singLookupNEq y = singLookupNNEq @x @σ y
  singLookupNEq _ = unsafeCoerce (Dict :: Dict ())

lookup :: CSingletonCtx x σ γ => Sing x -> ECtx sig γ -> LVal sig σ
lookup x (ECtx f) = f Dict x

-- Well-formed contexts --------------------------------

class ( CDiv γ 'Empty γ, CDiv  γ γ 'Empty
      , CMergeForward 'Empty γ γ, CMergeForward γ 'Empty γ
      ) 
    => WFCtx γ 
class (CDivN γ γ 'Empty) => WFNCtx γ

instance WFCtx 'Empty
instance WFNCtx γ => WFCtx ('N γ)
instance WFNCtx ('End σ)
instance WFNCtx γ => WFNCtx ('Cons 'Nothing γ)
instance WFNCtx γ => WFNCtx ('Cons ('Just σ) γ)


class CMergeU (u1 :: Maybe a) (u2 :: Maybe a) (u3 :: Maybe a)
      | u1 u2 -> u3, u1 u3 -> u2, u2 u3 -> u1 where

instance CMergeU (Nothing :: Maybe α) (Nothing :: Maybe α) (Nothing :: Maybe α)
instance CMergeU (Just a) (Nothing :: Maybe α) ('Just a :: Maybe α) where
instance CMergeU ('Nothing :: Maybe α) ('Just a) ('Just a :: Maybe α) where

class (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2
      , WFCtx g1, WFCtx g2, WFCtx g3) 
    => CMerge g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1

instance (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2
         , WFCtx g1, WFCtx g2, WFCtx g3)
    => CMerge g1 g2 g3 where

class (CMergeNForward g1 g2 g3, CMergeNForward g2 g1 g3, CDivN g3 g2 (N g1), CDivN g3 g1 (N g2)
      , WFNCtx g1, WFNCtx g2, WFNCtx g3) 
    => CMergeN g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1

instance (CMergeNForward g1 g2 g3, CMergeNForward g2 g1 g3, CDivN g3 g2 (N g1), CDivN g3 g1 (N g2)
      , WFNCtx g1, WFNCtx g2, WFNCtx g3) 
    => CMergeN g1 g2 g3


split :: forall γ1 γ2 γ sig. CMergeForward γ1 γ2 γ 
       => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
split (ECtx f) = (ECtx $ \Dict x -> f (lookupMerge1 @γ1 @γ2 @γ x) x
                 ,ECtx $ \Dict x -> f (lookupMerge2 @γ1 @γ2 @γ x) x)

class (MergeF γ1 γ2 ~ γ)
   => CMergeForward (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) | γ1 γ2 -> γ 
  where
    lookupMerge1 :: forall x σ. Lookup γ1 x ~ Just σ
                 => Sing x 
                 -> Dict (Lookup γ x ~ Just σ)
    lookupMerge2 :: Lookup γ2 x ~ Just σ
                 => Sing x 
                 -> Dict (Lookup γ x ~ Just σ)


class (MergeNF γ1 γ2 ~ γ)
   => CMergeNForward γ1 γ2 γ | γ1 γ2 -> γ where
--  lookupMergeN1 :: LookupN γ1 x ~ Just σ
--                => Sing x
--                -> Dict (LookupN γ x ~ Just σ)
--  lookupMergeN2 :: LookupN γ2 x ~ Just σ
--                => Sing x
--                -> Dict (LookupN γ x ~ Just σ)



instance CMergeForward ('Empty :: Ctx) ('Empty :: Ctx) ('Empty :: Ctx)
    -- lookupMerge1 and lookupMerge2 are inaccessible here
instance CMergeForward 'Empty ('N g) ('N g) where
    lookupMerge2 _ = Dict
    -- lookupMerge1 is inaccessible
instance CMergeForward ('N g) 'Empty ('N g) where
    lookupMerge1 _ = Dict
instance CMergeNForward g1 g2 g3 => CMergeForward ('N g1) ('N g2) ('N g3) where
--    lookupMerge1 x = lookupMergeN1 @g1 @g2 @g3 x
--    lookupMerge2 x = lookupMergeN2 @g1 @g2 @g3 x
    lookupMerge1 _ = unsafeCoerce (Dict :: Dict ())
    lookupMerge2 _ = unsafeCoerce (Dict :: Dict ())

instance CMergeNForward ('End σ) ('Cons 'Nothing g2) ('Cons ('Just σ) g2) where
--    lookupMergeN1 SZ     = Dict
--    lookupMergeN2 (SS _) = Dict
instance CMergeNForward ('Cons 'Nothing g1) ('End σ) ('Cons ('Just σ) g1) where
--    lookupMergeN1 (SS _) = Dict
--    lookupMergeN2 SZ     = Dict
-- u1=Nothing, u2=Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons 'Nothing g2) ('Cons 'Nothing g3) 
  where
--    lookupMergeN1 (SS x) = lookupMergeN1 @g1 @g2 @g3 x
--    lookupMergeN2 (SS x) = lookupMergeN2 @g1 @g2 @g3 x
-- u1=Just σ, u2= Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons ('Just σ) g1) ('Cons 'Nothing g2) ('Cons ('Just σ) g3) 
  where
--    lookupMergeN1 SZ = Dict
--    lookupMergeN1 (SS x) = lookupMergeN1 @g1 @g2 @g3 x
--    lookupMergeN2 (SS x) = lookupMergeN2 @g1 @g2 @g3 x
-- u1=Nothing, u2= Just σ
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons ('Just σ) g2) ('Cons ('Just σ) g3) 
  where
--    lookupMergeN1 (SS x) = lookupMergeN1 @g1 @g2 @g3 x
--    lookupMergeN2 SZ = Dict
--    lookupMergeN2 (SS x) = lookupMergeN2 @g1 @g2 @g3 x



-- Div ---------------------------------------

class (g3 ~ Div g1 g2)
   => CDiv (g1 :: Ctx) (g2 :: Ctx) (g3 :: Ctx) | g1 g2 -> g3 where

instance CDiv ('Empty :: Ctx) ('Empty :: Ctx) ('Empty :: Ctx) where
instance CDiv ('N g) 'Empty ('N g) where
instance CDivN g1 g2 g3 => CDiv ('N g1) ('N g2) g3 where

class (g3 ~ DivN g1 g2)
   => CDivN (g1 :: NCtx) (g2 :: NCtx) (g3 :: Ctx) | g1 g2 -> g3 where

instance σ ~ τ => CDivN ('End σ :: NCtx) ('End τ) ('Empty :: Ctx) where
instance CDivN ('Cons ('Just σ) g) ('End σ) ('N ('Cons 'Nothing g)) where
instance (CDivN g1 g2 g3, g3' ~ ConsN 'Nothing g3)
      => CDivN ('Cons 'Nothing g1) ('Cons 'Nothing g2) g3'
instance (CDivN g1 g2 g3, g3' ~ ConsN ('Just σ) g3)
      => CDivN ('Cons ('Just σ) g1) ('Cons 'Nothing g2) g3'
instance (CDivN g1 g2 g3, g3' ~ ConsN 'Nothing g3)
      => CDivN ('Cons ('Just σ) g1) ('Cons ('Just σ) g2) g3'
