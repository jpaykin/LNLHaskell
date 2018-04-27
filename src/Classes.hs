{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Classes where

import Prelude hiding (div)
import Data.Singletons
import GHC.TypeLits hiding (Div)
import Data.Constraint
import Data.Type.Equality
import Unsafe.Coerce
--import Debug.Trace

--import Prelim
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
  -- where
  --   addLookupNEq :: (x == y) ~ False
  --                => Proxy x -> Proxy y -> Dict (Lookup γ' y ~ Lookup γ y)

instance (γ' ~ AddF x σ γ, γ ~ Remove x γ', Lookup γ' x ~ Just σ
         , KnownNat x)
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 

addLookupNEq :: (γ' ~ AddF x σ γ, (x == y) ~ False)
             => Proxy x -> Proxy y -> Dict (Lookup γ' y ~ Lookup γ y)
addLookupNEq _ _ = unsafeCoerce (Dict :: Dict ())


-- Singleton Contexts ------------------------------------------

class (γ ~ SingletonF x σ, Remove x γ ~ '[], Lookup γ x ~ 'Just σ, KnownNat x
      ,γ ~ '[ '(x,σ) ])
   => CSingletonCtx (x :: Nat) (σ :: LType) (γ :: Ctx)
      | x σ -> γ, γ -> x σ 

instance (γ ~ SingletonF x σ
         , Remove x γ ~ '[]
         , Lookup γ x ~ 'Just σ
         , KnownNat x
         , γ ~ '[ '(x,σ) ])
   => CSingletonCtx (x :: Nat) (σ :: LType) (γ :: Ctx)

singletonLookupNEq :: forall x y σ. (x == y) ~ False 
                   => Proxy y -> Dict (Lookup '[ '(x,σ) ] y ~ Nothing)
singletonLookupNEq _ = unsafeCoerce (Dict :: Dict ())


-- Merging ---------------------------------------



class (γ ~ MergeF γ1 γ2, γ ~ MergeF γ2 γ1, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
      , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge' γ1 γ2 γ | γ1 γ2 -> γ, γ1 γ -> γ2, γ2 γ -> γ1

instance (γ ~ MergeF γ1 γ2, γ ~ MergeF γ2 γ1, Div γ γ2 ~ γ1, Div γ γ1 ~ γ2
      , WFCtx γ1, WFCtx γ2, WFCtx γ)
    => CMerge' γ1 γ2 γ 

type CMerge γ1 γ2 γ = (CMerge' γ1 γ2 γ, KnownDomain γ1, KnownDomain γ2, KnownDomain γ)

lookupMerge1 :: forall γ1 γ2 γ x σ.
                (γ ~ MergeF γ1 γ2, Lookup γ1 x ~ Just σ)
             => Proxy x 
             -> Dict (Lookup γ x ~ Just σ)
lookupMerge1 _ = unsafeCoerce (Dict :: Dict ())

lookupMerge2 :: forall γ1 γ2 γ x σ.
                (γ ~ MergeF γ1 γ2, Lookup γ2 x ~ Just σ)
             => Proxy x 
             -> Dict (Lookup γ x ~ Just σ)

lookupMerge2 _ = unsafeCoerce (Dict :: Dict ())


{-
split :: forall γ1 γ2 γ sig. CMerge γ1 γ2 γ 
       => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
split (ECtx f) = (ECtx $ \Dict x -> f (lookupMerge1 @γ1 @γ2 @γ x) x
                 ,ECtx $ \Dict x -> f (lookupMerge2 @γ1 @γ2 @γ x) x)
-}



-- Well-formed contexts --------------------------------



type WFCtx' γ = (Div γ '[] ~ γ, Div  γ γ ~ '[]
               , MergeF '[] γ ~ γ, MergeF γ '[] ~ γ)
--               , KnownDomain γ )
class (WFCtx' γ) => WFCtx γ
instance (WFCtx' γ) => WFCtx γ
type WFCtxDict = (((),(),(),()) :: Constraint)

unsafeWFCtx :: forall γ. Dict (WFCtx γ)
unsafeWFCtx = unsafeCoerce (Dict :: Dict ())


-- Helper stuff -----------------------------------


type WFVar' x σ γ = ( CSingletonCtx x σ (SingletonF x σ)
                   , CAddCtx x σ γ (AddF x σ γ) 
                   , CMerge' γ (SingletonF x σ) (AddF x σ γ)
                   , CMerge' (SingletonF x σ) γ (AddF x σ γ)
                   , WFCtx γ
                   , WFCtx (AddF x σ γ)
                   , Lookup γ x ~ 'Nothing
                   )
type WFVar x σ γ = (WFVar' x σ γ, KnownDomain γ, KnownDomain (AddF x σ γ))
type WFVarDict = (((),(),(),(),(),()) :: Constraint)
type WFFresh σ γ = WFVar (Fresh γ) σ γ

unsafeWFVar' :: forall x σ γ. Dict (WFVar' x σ γ)
unsafeWFVar' = unsafeCoerce (Dict :: Dict ((),(),(),(),(),(),()))


-- wfFresh is actually safe
wfFresh :: forall σ γ. KnownDomain γ => Dict (WFFresh σ γ)
wfFresh = case unsafeWFVar' @(Fresh γ) @σ @γ of 
            Dict -> case addDomain @(Fresh γ) @σ @γ of 
              Dict -> Dict


class ( x ~ Fresh γ
      , WFVar' x σ γ1, WFVar' x σ γ2
      , CMerge' (AddF x σ γ1) γ2 (AddF x σ γ)
      , CMerge' γ1 (AddF x σ γ2) (AddF x σ γ)
      )
  => WFVarMerge x σ γ1 γ2 γ
instance ( x ~ Fresh γ
         , WFVar' x σ γ1, WFVar' x σ γ2
         , CMerge' (AddF x σ γ1) γ2 (AddF x σ γ)
         , CMerge' γ1 (AddF x σ γ2) (AddF x σ γ)
         )
  => WFVarMerge x σ γ1 γ2 γ


wfFreshMerge' :: forall x σ γ1 γ2 γ. (x ~ Fresh γ, CMerge γ1 γ2 γ)
              => Dict (WFVarMerge x σ γ1 γ2 γ)
wfFreshMerge' = unsafeCoerce (Dict :: Dict ())

wfFreshMerge ::  forall x σ γ1 γ2 γ. (x ~ Fresh γ, CMerge γ1 γ2 γ)
              => Dict ( KnownDomain (AddF x σ γ1)
                      , KnownDomain (AddF x σ γ2)
                      , KnownDomain (AddF x σ γ)
                      , WFVarMerge x σ γ1 γ2 γ)
wfFreshMerge = case knownFresh @γ of
                 Dict -> case ( wfFreshMerge' @x @σ @γ1 @γ2 @γ
                              , addDomain @x @σ @γ1
                              , addDomain @x @σ @γ2
                              , addDomain @x @σ @γ ) of
                          (Dict,Dict,Dict,Dict) -> Dict


class  ( x ~ Fresh γ, y ~ Fresh (AddF x σ γ)
       , WFVar' x σ γ, WFVar' y τ (AddF x σ γ)
       , WFVar' y τ γ, WFVar' x σ (AddF y τ γ)
       , CAddCtx x σ (AddF y τ γ) γ'
       , CAddCtx y τ (AddF x σ γ) γ'
       , AddF x σ (AddF y τ γ) ~ AddF y τ (AddF x σ γ)
       )
  => WFVarTwo x σ y τ γ γ'
     | γ σ -> x y
instance  ( x ~ Fresh γ, y ~ Fresh (AddF x σ γ)
          , WFVar' x σ γ, WFVar' y τ (AddF x σ γ)
          , WFVar' y τ γ, WFVar' x σ (AddF y τ γ)
          , CAddCtx x σ (AddF y τ γ) γ'
          , CAddCtx y τ (AddF x σ γ) γ'
--          , AddF x σ (AddF y τ γ) ~ AddF y τ (AddF x σ γ)
          , CMerge' (AddF y τ γ) (SingletonF x σ) (AddF y τ (AddF x σ γ))
          )
  => WFVarTwo x σ y τ γ γ'

wfVarTwo' :: forall γ σ τ x y.
            (x ~ Fresh γ, y ~ Fresh (AddF x σ γ))
         => Dict (WFVarTwo x σ y τ γ (AddF x σ (AddF y τ γ)))
wfVarTwo' = unsafeCoerce (Dict :: Dict ())

wfVarTwo ::  forall γ σ τ x y.
            (x ~ Fresh γ, y ~ Fresh (AddF x σ γ), KnownDomain γ)
         => Dict ( WFVarTwo x σ y τ γ (AddF x σ (AddF y τ γ))
                 , KnownDomain (AddF y τ γ)
                 , KnownDomain (AddF x σ γ)
                 , KnownDomain (AddF x σ (AddF y τ γ))
                 , KnownDomain (AddF y τ (AddF x σ γ)) )
wfVarTwo = case wfVarTwo' @γ @σ @τ @x @y of
  Dict -> case knownFresh @γ of                    -- KnownNat x
    Dict -> case addDomain @x @σ @γ of                -- KnownDomain (γ,x:σ)
      Dict -> case knownFresh @(AddF x σ γ) of        -- KnownNat y
        Dict -> case addDomain @y @τ @(AddF x σ γ) of -- KnownDomain (γ,x:σ,y:τ)
          Dict -> case addDomain @y @τ @γ of          -- KnownDomain (γ,y:τ)
            Dict -> case addDomain @x @σ @(AddF y τ γ) of -- KnownDomain (γ,y:τ,x:σ)
              Dict -> Dict

-- Remove y (AddF y τ (AddF x σ γ)) ~ AddF x σ γ
-- CAdd y τ (AddF x σ γ) (AddF y τ (AddF x σ γ))
