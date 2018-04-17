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
import GHC.TypeLits
import Data.Constraint
import Data.Type.Equality
import Unsafe.Coerce

import Prelim
import Types

-- In Context ---------------------------------------------

class CIn (x :: Nat) (σ :: LType) (γ :: Ctx)

instance CIn x σ ('(x,σ) ': γ)
instance (CIn x σ γ) => CIn x σ ('(y,τ) ': γ)

-- Add To Context --------------------------------------------

class (γ' ~ AddF x σ γ, γ ~ Remove x γ', Lookup γ' x ~ Just σ
      , KnownNat x)
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 
    | x σ γ -> γ', x γ' -> σ γ
  where
    addLookupNEq :: (x == y) ~ False
                 => Proxy x -> Proxy y -> Dict (Lookup γ' y ~ Lookup γ y)

instance (γ' ~ AddF x σ γ, γ ~ Remove x γ', Lookup γ' x ~ Just σ
         , KnownNat x)
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 
  where
    addLookupNEq _ _ = unsafeCoerce (Dict :: Dict ())

add :: forall σ γ γ' x sig. CAddCtx x σ γ γ' 
    => Proxy x -> LVal sig σ -> ECtx sig γ -> ECtx sig γ'
add x v (ECtx f) = ECtx $ \Dict y -> -- Lookup γ y ~ Just τ
    case eqSNat x y of
      Left  Dict -> v
      Right Dict -> case addLookupNEq @x @σ @γ @γ' x y of Dict -> f Dict y

-- Singleton Contexts ------------------------------------------

class (γ ~ SingletonF x σ, Remove x γ ~ '[], Lookup γ x ~ 'Just σ, KnownNat x)
   => CSingletonCtx (x :: Nat) (σ :: LType) (γ :: Ctx)
      | x σ -> γ, γ -> x σ 
  where
    singletonLookupNEq :: forall y.  (x == y) ~ False 
                       => Proxy y -> Dict (Lookup γ y ~ Nothing)

instance (γ ~ SingletonF x σ, Remove x γ ~ '[], Lookup γ x ~ 'Just σ, KnownNat x)
   => CSingletonCtx (x :: Nat) (σ :: LType) (γ :: Ctx)
  where
    singletonLookupNEq _ = unsafeCoerce (Dict :: Dict ())

lookup :: CSingletonCtx x σ γ => Proxy x -> ECtx sig γ -> LVal sig σ
lookup x (ECtx f) = f Dict x

-- Merging ---------------------------------------

{-
class (MergeF γ1 γ2 ~ γ)
   => CMergeForward (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) | γ1 γ2 -> γ 
  where
    lookupMerge1 :: forall x σ. Dict (Lookup γ1 x ~ Just σ)
                 -> Proxy x 
                 -> Dict (Lookup γ x ~ Just σ)
    lookupMerge2 :: Dict (Lookup γ2 x ~ Just σ)
                 -> Proxy x 
                 -> Dict (Lookup γ x ~ Just σ)

instance (MergeF γ1 γ2 ~ γ)
   => CMergeForward (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx)
  where
    lookupMerge1 _ _ = unsafeCoerce (Dict :: Dict ())
    lookupMerge2 _ _ = unsafeCoerce (Dict :: Dict ())
-}


class (γ ~ MergeF γ1 γ2, γ ~ MergeF γ2 γ1, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
      , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge γ1 γ2 γ | γ1 γ2 -> γ, γ1 γ -> γ2, γ2 γ -> γ1
  where
    lookupMerge1 :: Lookup γ1 x ~ Just σ
                 => Proxy x 
                 -> Dict (Lookup γ x ~ Just σ)
    lookupMerge2 :: Lookup γ2 x ~ Just σ
                 => Proxy x 
                 -> Dict (Lookup γ x ~ Just σ)

instance (γ ~ MergeF γ1 γ2, γ ~ MergeF γ2 γ1, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
      , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge γ1 γ2 γ 
  where
    lookupMerge1 _ = unsafeCoerce (Dict :: Dict ())
    lookupMerge2 _ = unsafeCoerce (Dict :: Dict ())


split :: forall γ1 γ2 γ sig. CMerge γ1 γ2 γ 
       => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
split (ECtx f) = (ECtx $ \Dict x -> f (lookupMerge1 @γ1 @γ2 @γ x) x
                 ,ECtx $ \Dict x -> f (lookupMerge2 @γ1 @γ2 @γ x) x)



-- Well-formed contexts --------------------------------

type WFCtx γ = (Div γ '[] ~ γ, Div  γ γ ~ '[]
               , MergeF '[] γ ~ γ, MergeF γ '[] ~ γ ) 


-- Helper stuff -----------------------------------


type WFVar x σ γ = ( CSingletonCtx x σ (SingletonF x σ)
                   , CAddCtx x σ γ (AddF x σ γ) 
                   , CMerge γ (SingletonF x σ) (AddF x σ γ)
                   , WFCtx γ
                   )
class WFVar (Fresh γ) σ γ => WFFresh σ γ
instance WFVar (Fresh γ) σ γ => WFFresh σ γ
