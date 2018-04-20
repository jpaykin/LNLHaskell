{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, EmptyCase, FlexibleContexts, TypeFamilyDependencies
           , RankNTypes
#-}

module Types where

import Prelim

import Data.Kind
import GHC.TypeLits
import Data.Proxy
import Data.Singletons
import Data.Constraint
import Prelude hiding (lookup)

data LType where MkLType :: ty LType -> LType
  -- ty :: * -> *

type Sig = Ctx -> LType -> Type
--type Exp = Ctx -> LType -> Type
type Val = LType -> Type

--data family LExp (sig :: Sig) :: Exp
data family LVal (sig :: Sig) :: Val
type family Effect (sig :: Sig) :: Type -> Type

type Ctx = [(Nat,LType)]


--data Ctx  = Empty | N (NCtx)
--data NCtx = End (Nat,LType) | Cons (Maybe (Nat,LType)) (NCtx)


-- data instance Sing (γ :: Ctx) where
--   SSEmpty :: Sing ([] :: Ctx)
--   SSCons  :: Sing u -> Sing (γ :: Ctx) -> Sing (u':γ)
-- data instance Sing (m :: Maybe α) where
--   SSNothing :: Sing Nothing
--   SSJust    :: Sing (Just a) -- cuts off
-- instance SingI ('[] :: Ctx) where sing = SSEmpty
-- instance (SingI u, SingI (γ :: Ctx)) => SingI (u ': γ) 
--     where sing = SSCons (sing :: Sing u) sing
-- instance SingI Nothing  where sing = SSNothing
-- instance SingI (Just a) where sing = SSJust

{-
data SCtx sig (γ :: Ctx) where
  SEmpty :: SCtx sig '[]
  SCons  :: SMaybe sig u -> SCtx sig γ -> SCtx sig (u':γ)
data SMaybe sig (u :: Maybe (Nat,LType)) where
  SNothing :: SMaybe sig Nothing
  SJust    :: KnownNat x => LVal sig σ -> SMaybe sig (Just '(x,σ))
-}

-- Define an evaluation context that may have extra entries, which makes
-- splitting a context a no-op, increasing performance.

data ECtx sig (γ :: Ctx) where
  ECtx :: (forall x σ. KnownNat x => 
                       Dict (Lookup γ x ~ Just σ) -> Proxy x -> LVal sig σ) 
       -> ECtx sig γ

eEmpty :: ECtx sig '[]
eEmpty = ECtx (\d x -> case d of)

data ECtx' sig γ where
  ENil  :: ECtx' sig '[]
  ECons :: Sing x -> LVal sig σ → ECtx' sig γ → ECtx' sig ('(x,σ) ': γ)

{-

data EVal sig where
  EVal :: !(LVal sig σ) -> EVal sig

type ECtx'' sig γ = IntMap (EVal sig)

lookup :: KnownNat z => Dict (Lookup γ x ~ 'Just σ) -> ECtx' sig γ -> Sing z -> LVal sig σ
lookup d ENil _ = case d of
lookup d (ECons x v γ') z = case eqSNat x z of
    Left Dict -> v
    Right Dict -> case addLookupNEq x z of Dict -> lookup Dict γ' z
-}

-- Fresh variables ------------------------------------------

type family Fresh (γ :: Ctx) :: Nat where
  Fresh '[] = 0
  Fresh '[ '(x,_) ] = x+1
  Fresh (_ ': γ)    = Fresh γ -- since contexts are ordered

-- Type families

type family Lookup (γ :: Ctx) (x :: Nat) :: Maybe LType where
  Lookup '[] _        = Nothing
  Lookup ('(y,σ):γ) x = If (x ==? y) ('Just σ) (Lookup γ x)
  
type family Remove (x :: Nat) (γ :: Ctx) :: Ctx where
  Remove x '[]           = TypeError (Text "Error in Remove")
  Remove x ('(y,σ) ': γ) = CompareOrd (CmpNat x y)
                                      (TypeError (Text "Error in Remove")) -- x < y
                                      γ -- x == y
                                      ('(y,σ) ': Remove x γ) -- x > y


type family Div (γ :: Ctx) (γ0 :: Ctx) = (r :: Ctx) where
  Div γ '[]            = γ
  Div γ ('(x,_) ': γ0) = Remove x (Div γ γ0)
--  Div '[]            _  = '[]
--  Div ('(x,_) ': γ) γ0  = Div γ (Remove x γ0)

type family SingletonF x (σ :: LType) :: Ctx where
  SingletonF x σ = '[ '(x,σ) ]

-- insertion sort
type family AddF (x :: Nat) (σ :: LType) (γ :: Ctx) :: Ctx where
  AddF x σ '[] = '[ '(x,σ) ]
  AddF x σ ('(y,τ) ': γ) = CompareOrd (CmpNat x y) 
                                      ('(x,σ) ': '(y,τ) ': γ) -- x < y
                                      (TypeError (Text "Error in AddF")) -- x == y
                                      ('(y,τ) ': AddF x σ γ) -- x > y


--If (x ==? y) (TypeError (Text "Error in AddF")) 
--                                        ('(y,τ) ': AddF x σ γ)

type family MergeF (γ1 :: Ctx) (γ2 :: Ctx) :: Ctx where
  MergeF '[] γ2 = γ2
  MergeF ('(x,σ) ': γ1) γ2 = MergeF γ1 (AddF x σ γ2)
