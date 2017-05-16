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

class CIn  (x :: Nat) (σ :: LType) (γ :: Ctx)
class CInN (x :: Nat) (σ :: LType) (γ :: NCtx)

instance CInN 'Z σ ('End σ)
instance CInN 'Z σ ('Cons ('Just σ) γ)
instance (CInN x σ γ) => CInN ('S x) σ ('Cons u γ)

instance CInN x σ γ => CIn x σ ('N γ)
  

-- Add To Context ----------------------------------------------


add :: forall σ γ γ' x sig. CAddCtx x σ γ γ' 
    => Sing x -> LVal sig σ -> ECtx sig γ -> ECtx sig γ'
add x v (ECtx f) = ECtx $ \Dict y -> case eqSNat x y of
  Left  Dict -> v
  Right Dict -> case addLookupNEq @x @σ @γ @γ' x y of Dict -> f Dict y


class (γ' ~ AddF x σ γ, γ ~ Remove x γ', Lookup γ' x ~ Just σ)
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 
    | x σ γ -> γ', x γ' -> σ γ
  where
    addLookupNEq :: (x == y) ~ False 
                 => Sing x -> Sing y -> Dict (Lookup γ' y ~ Lookup γ y)

instance (CAddCtx' x σ γ γ' (CountNMinus1 γ')) => 
         CAddCtx x σ γ (N γ')
  where
--    addLookupNEq _ = addLookupNNEq @x @σ @γ @γ'
    addLookupNEq _ = unsafeCoerce (Dict :: Dict ())

class ( γ' ~ AddNNF x σ γ, N γ ~ RemoveN x γ'
      , len ~ CountN γ, LookupN γ' x ~ Just σ)
    => CAddNCtx' (x :: Nat) (σ :: LType) (γ :: NCtx) (γ' :: NCtx) (len :: Nat)
    | x σ γ -> γ' len, x γ' len -> σ γ
--  where
--    addLookupNNNEq :: (x == y) ~ False 
--                   => Sing y -> Dict (LookupN γ' y ~ LookupN γ y)

instance (CountN γ ~ len, WFNCtx γ)
      => CAddNCtx' Z σ (Cons Nothing γ) (Cons (Just σ) γ) len
--  where
--    addLookupNNNEq (SS _) = Dict
instance (CSingletonNCtx x σ γ', WFNCtx γ')
      => CAddNCtx' (S x) σ (End τ) (Cons (Just τ) γ') (S Z)
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = singLookupNNEq @x @σ y
instance CAddNCtx' x (σ :: LType) (γ :: NCtx) (γ' :: NCtx) n
      => CAddNCtx' (S x) σ (Cons Nothing γ) (Cons Nothing γ') n
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = addLookupNNNEq @x @σ @γ y
instance CAddNCtx' x (σ :: LType) (γ :: NCtx) (γ' :: NCtx) (S n)
      => CAddNCtx' (S x) σ (Cons (Just τ) γ) (Cons (Just τ) γ') (S (S n))
--  where
--    addLookupNNNEq SZ = Dict
--    addLookupNNNEq (SS y) = addLookupNNNEq @x @σ @γ y

class ( γ' ~ AddNF x σ γ, γ ~ RemoveN x γ'
      , len ~ Count γ -- ~ Count γ
      , LookupN γ' x ~ Just σ)
   => CAddCtx' (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: NCtx) (len :: Nat)
    | x σ γ -> len γ', x γ' len -> σ γ 
--  where
--    addLookupNNEq :: (x == y) ~ False 
--                  => Sing y -> Dict (LookupN γ' y ~ Lookup γ y)

instance CAddNCtx' x σ γ γ' (S len) => CAddCtx' x σ (N γ) γ' (S len)
--  where
--    addLookupNNEq = addLookupNNNEq @x @σ @γ
instance CSingletonNCtx x σ γ'  => CAddCtx' x σ Empty γ' Z
--  where
--    addLookupNNEq = singLookupNEq @x @σ

---------------------

-- outputs the number of variables used in the NCtx
-- since every NCtx has size >= 1, we first compute |γ|-1 and then add one.
type family CountNMinus1 γ :: Nat where
  CountNMinus1 ('End _) = 'Z
  CountNMinus1 ('Cons ('Just _) γ) = 'S (CountNMinus1 γ)
  CountNMinus1 ('Cons 'Nothing γ)  = CountNMinus1 γ
type CountN γ = S (CountNMinus1 γ)
type family Count γ :: Nat where
  Count Empty = 'Z
  Count (N γ) = CountN γ

type family IsSingletonF  γ :: Bool where
  IsSingletonF ('End σ)            = 'True
  IsSingletonF ('Cons ('Just _) _) = 'False
  IsSingletonF ('Cons 'Nothing   γ) = IsSingletonF γ

type family IsDouble γ :: Bool where
  IsDouble ('End σ) = 'False
  IsDouble ('Cons ('Just _) γ) = IsSingletonF γ
  IsDouble ('Cons 'Nothing γ)   = IsDouble γ

class CIsSingleton (γ :: NCtx) (flag :: Bool) | γ -> flag where

instance CIsSingleton ('End σ) 'True where
instance CIsSingleton ('Cons ('Just σ) γ) 'False where
instance CIsSingleton γ b => CIsSingleton ('Cons 'Nothing γ) b where

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

class (γ ~ SingletonF x σ, Remove x γ ~ Empty, Lookup γ x ~ Just σ, SingI x)
   => CSingletonCtx (x :: Nat) (σ :: LType) (γ :: Ctx) 
      | x σ -> γ, γ -> x σ where
  singLookupNEq :: forall y.  (x == y) ~ False 
                => Sing y -> Dict (Lookup γ y ~ Nothing)
class (γ ~ SingletonNF x σ, RemoveN x γ ~ Empty, CountNMinus1 γ ~ Z
      , LookupN γ x ~ Just σ, SingI x)
   => CSingletonNCtx (x :: Nat) (σ :: LType) (γ :: NCtx) 
    | x σ -> γ, γ -> x σ where
  singLookupNNEq :: forall y. (x == y) ~ False 
                 => Sing y -> Dict (LookupN γ y ~ Nothing)

instance CSingletonNCtx 'Z σ ('End σ) where
  singLookupNNEq (SS _) = Dict
instance CSingletonNCtx x σ γ => CSingletonNCtx ('S x) σ ('Cons 'Nothing γ) where
  singLookupNNEq SZ = Dict
  singLookupNNEq (SS y) = singLookupNNEq @x @σ y
instance CSingletonNCtx x σ γ => CSingletonCtx x σ ('N γ) where
  singLookupNEq y = singLookupNNEq @x @σ y
--  singLookupNEq _ = unsafeCoerce (Dict :: Dict ())

lookup :: CSingletonCtx x σ γ => Sing x -> ECtx sig γ -> LVal sig σ
lookup x (ECtx f) = f Dict x

-- Well-formed contexts --------------------------------

class ( Div γ 'Empty ~ γ, Div  γ γ ~ 'Empty
      , CMergeForward 'Empty γ γ, CMergeForward γ 'Empty γ
      ) 
    => WFCtx γ 
class (DivN γ γ ~ 'Empty) => WFNCtx γ

instance WFCtx 'Empty
instance WFNCtx γ => WFCtx ('N γ)
instance WFNCtx ('End σ)
instance WFNCtx γ => WFNCtx ('Cons 'Nothing γ)
instance WFNCtx γ => WFNCtx ('Cons ('Just σ) γ)

-- Merging ---------------------------------------

split :: forall γ1 γ2 γ sig. CMerge γ1 γ2 γ 
       => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
split (ECtx f) = (ECtx $ \Dict x -> f (lookupMerge1 @γ1 @γ2 @γ Dict x) x
                 ,ECtx $ \Dict x -> f (lookupMerge2 @γ1 @γ2 @γ Dict x) x)


class (CMergeForward γ1 γ2 γ, CMergeForward γ2 γ1 γ, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
      , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge γ1 γ2 γ | γ1 γ2 -> γ, γ1 γ -> γ2, γ2 γ -> γ1

instance (CMergeForward γ1 γ2 γ, CMergeForward γ2 γ1 γ, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
         , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge γ1 γ2 γ where

class (CMergeNForward γ1 γ2 γ, CMergeNForward γ2 γ1 γ, DivN γ γ2 ~ N γ1, DivN γ γ1 ~ N γ2
      , WFNCtx γ1, WFNCtx γ2, WFNCtx γ) 
    => CMergeN γ1 γ2 γ | γ1 γ2 -> γ, γ1 γ -> γ2, γ2 γ -> γ1

instance (CMergeNForward γ1 γ2 γ, CMergeNForward γ2 γ1 γ, DivN γ γ2 ~ N γ1, DivN γ γ1 ~ N γ2
      , WFNCtx γ1, WFNCtx γ2, WFNCtx γ) 
    => CMergeN γ1 γ2 γ



class (MergeF γ1 γ2 ~ γ)
   => CMergeForward (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) | γ1 γ2 -> γ 
  where
    lookupMerge1 :: forall x σ. Dict (Lookup γ1 x ~ Just σ)
                 -> Sing x 
                 -> Dict (Lookup γ x ~ Just σ)
    lookupMerge2 :: Dict (Lookup γ2 x ~ Just σ)
                 -> Sing x 
                 -> Dict (Lookup γ x ~ Just σ)


class (MergeNF γ1 γ2 ~ γ)
   => CMergeNForward γ1 γ2 γ | γ1 γ2 -> γ where
 lookupMergeN1 :: LookupN γ1 x ~ Just σ
               => Sing x
               -> Dict (LookupN γ x ~ Just σ)
 lookupMergeN2 :: LookupN γ2 x ~ Just σ
               => Sing x
               -> Dict (LookupN γ x ~ Just σ)



instance CMergeForward ('Empty :: Ctx) ('Empty :: Ctx) ('Empty :: Ctx)
  where
    lookupMerge1 pf = case pf of 
    lookupMerge2 pf = case pf of
instance CMergeForward 'Empty ('N g) ('N g) where
    lookupMerge1 pf = case pf of
    lookupMerge2 Dict _ = Dict
    -- lookupMerge1 is inaccessible
instance CMergeForward ('N g) 'Empty ('N g) where
    lookupMerge1 Dict _ = Dict
    lookupMerge2 pf = case pf of
instance CMergeNForward γ1 γ2 γ => CMergeForward ('N γ1) ('N γ2) ('N γ) where
    lookupMerge1 Dict x = lookupMergeN1 @γ1 @γ2 @γ x
    lookupMerge2 Dict x = lookupMergeN2 @γ1 @γ2 @γ x
--    lookupMerge1 _ = unsafeCoerce (Dict :: Dict ())
--    lookupMerge2 _ = unsafeCoerce (Dict :: Dict ())

instance CMergeNForward ('End σ) ('Cons 'Nothing γ2) ('Cons ('Just σ) γ2) where
    lookupMergeN1 SZ     = Dict
    lookupMergeN2 (SS _) = Dict
instance CMergeNForward ('Cons 'Nothing γ1) ('End σ) ('Cons ('Just σ) γ1) where
    lookupMergeN1 (SS _) = Dict
    lookupMergeN2 SZ     = Dict
-- u1=Nothing, u2=Nothing
instance CMergeNForward γ1 γ2 γ
    => CMergeNForward ('Cons 'Nothing γ1) ('Cons 'Nothing γ2) ('Cons 'Nothing γ) 
  where
    lookupMergeN1 (SS x) = lookupMergeN1 @γ1 @γ2 @γ x
    lookupMergeN2 (SS x) = lookupMergeN2 @γ1 @γ2 @γ x
-- u1=Just σ, u2= Nothing
instance CMergeNForward γ1 γ2 γ
    => CMergeNForward ('Cons ('Just σ) γ1) ('Cons 'Nothing γ2) ('Cons ('Just σ) γ) 
  where
    lookupMergeN1 SZ = Dict
    lookupMergeN1 (SS x) = lookupMergeN1 @γ1 @γ2 @γ x
    lookupMergeN2 (SS x) = lookupMergeN2 @γ1 @γ2 @γ x
-- u1=Nothing, u2= Just σ
instance CMergeNForward γ1 γ2 γ
    => CMergeNForward ('Cons 'Nothing γ1) ('Cons ('Just σ) γ2) ('Cons ('Just σ) γ) 
  where
    lookupMergeN1 (SS x) = lookupMergeN1 @γ1 @γ2 @γ x
    lookupMergeN2 SZ = Dict
    lookupMergeN2 (SS x) = lookupMergeN2 @γ1 @γ2 @γ x

