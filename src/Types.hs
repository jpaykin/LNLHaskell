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
import GHC.TypeLits hiding (Nat) --  (TypeError, ErrorMessage(..))
import Data.Proxy
import Data.Singletons
import Data.Constraint

data LType where MkLType :: ty LType -> LType
  -- ty :: * -> *

type Sig = Type
type Exp = Ctx -> LType -> Type
type Val = LType -> Type

data family LExp (sig :: Sig) :: Exp
data family LVal (sig :: Sig) :: Val
type family Effect (sig :: Sig) :: Type -> Type


data Ctx  = Empty | N (NCtx)
data NCtx = End (LType) | Cons (Maybe (LType)) (NCtx)

data instance Sing (γ :: Ctx) where
  SSEmpty :: Sing Empty
  SSN     :: Sing γ -> Sing (N γ)
data instance Sing (γ :: NCtx) where
  SSEnd  :: Sing (End σ)
  SSCons :: Sing u -> Sing γ -> Sing (Cons u γ)
data instance Sing (m :: Maybe α) where
  SSNothing :: Sing Nothing
  SSJust    :: Sing (Just a) -- cuts off
instance SingI Empty where sing = SSEmpty
instance SingI γ => SingI (N γ) where sing = SSN sing
instance SingI (End σ) where sing = SSEnd
instance (SingI u, SingI γ) => SingI (Cons u γ) where
  sing = SSCons sing sing
instance SingI Nothing where sing = SSNothing
instance SingI (Just a) where sing = SSJust

data SCtx sig (γ :: Ctx) where
  SEmpty :: SCtx sig Empty
  SN     :: SNCtx sig γ -> SCtx sig (N γ)
data SNCtx sig (γ :: NCtx) where
  SEnd   :: LVal sig σ   -> SNCtx sig (End σ)
  SCons  :: SMaybe sig u -> SNCtx sig γ -> SNCtx sig ('Cons u γ)
data SMaybe sig (u :: Maybe LType) where
  SNothing :: SMaybe sig 'Nothing
  SJust    :: LVal sig σ -> SMaybe sig ('Just σ)

-- Define an evaluation context that may have extra entries, which makes
-- splitting a context a no-op, increasing performance.

data ECtx sig γ where
  ECtx :: (forall x σ. Dict (Lookup γ x ~ Just σ) -> Sing x -> LVal sig σ) 
       -> ECtx sig γ

eEmpty :: ECtx sig Empty
eEmpty = ECtx (\d x -> case d of)

type family ConsN (u :: Maybe (LType)) (g :: Ctx) :: Ctx where
  ConsN ('Just σ) 'Empty = 'N ('End σ)
  ConsN 'Nothing   'Empty = 'Empty
  ConsN u         ('N g) = 'N ('Cons u g)


-- Fresh variables ------------------------------------------

type family FreshN (g :: NCtx) :: Nat where
  FreshN ('End τ)            = 'S 'Z
  FreshN ('Cons 'Nothing g)   = 'Z
  FreshN ('Cons ('Just σ) g) = 'S (FreshN g)

type family Fresh (g::Ctx) :: Nat where
  Fresh 'Empty = 'Z
  Fresh ('N g) = FreshN g

type family FreshN2 g :: Nat where
  FreshN2 ('End τ)            = 'S ('S 'Z)
  FreshN2 ('Cons 'Nothing g)  = 'S (FreshN g)
  FreshN2 ('Cons ('Just σ) g) = 'S (FreshN2 g)

type family Fresh2 (g::Ctx) :: Nat where
  Fresh2 'Empty = 'S 'Z
  Fresh2 ('N g) = FreshN2 g

fresh :: forall γ. SingI γ => Sing (Fresh γ)
fresh = case (sing :: Sing γ) of
          SSEmpty -> SZ
          SSN γ   -> freshN γ
freshN :: forall γ. Sing γ -> Sing (FreshN γ)
freshN SSEnd                = (SS SZ)
freshN (SSCons SSNothing _) = SZ
freshN (SSCons SSJust γ)    = SS $ freshN γ


-- Type families
type family MaybeError (m :: Maybe a) err :: a where
  MaybeError (Just a) err = a
  MaybeError Nothing  err = TypeError err

type family Lookup (γ :: Ctx) (x :: Nat) :: Maybe LType where
  Lookup Empty x = Nothing
  Lookup (N γ) x = LookupN γ x
type family LookupN (γ :: NCtx) (x :: Nat) :: Maybe LType where
  LookupN (End σ)    Z     = Just σ
  LookupN (End _)    (S _) = Nothing
  LookupN (Cons u _) Z     = u
  LookupN (Cons _ γ) (S x) = LookupN γ x
  

type family Div (γ :: Ctx) (γ0 :: Ctx) = (r :: Ctx) where
  Div γ      'Empty  = γ
  Div ('N γ) ('N γ0) = DivN γ γ0
  Div γ      γ0      = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

type family DivN (γ :: NCtx) (γ0 :: NCtx) = (r :: Ctx) where
  DivN ('End _)            ('End _)             = 'Empty
  DivN ('Cons ('Just _) γ) ('End _)             = 'N ('Cons 'Nothing γ)
  DivN ('Cons ('Just _) γ) ('Cons ('Just _) γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN ('Cons ('Just σ) γ) ('Cons 'Nothing γ0)  = ConsN ('Just σ) (DivN γ γ0)
  DivN ('Cons 'Nothing  γ) ('Cons 'Nothing  γ0) = ConsN 'Nothing  (DivN γ γ0)
  DivN γ                   γ0                   = TypeError
    (ShowType γ0 :<>: Text " must be a subcontext of " :<>: ShowType γ)

type family SingletonNF x (σ :: LType) :: NCtx where
  SingletonNF x σ = AddNF x σ 'Empty
type family SingletonF x (σ :: LType) :: Ctx where
  SingletonF x σ = 'N (SingletonNF x σ)


type family AddF (x :: Nat) (σ :: LType) (g :: Ctx) :: Ctx where
  AddF x σ g = 'N (AddNF x σ g)

type family AddNF (x :: Nat) (σ :: LType) (g :: Ctx) :: NCtx where
  AddNF 'Z     σ 'Empty = 'End σ
  AddNF ('S x) σ 'Empty = 'Cons 'Nothing (AddNF x σ 'Empty)
  AddNF x      σ ('N g) = AddNNF x σ g

type family AddNNF x σ (g :: NCtx) :: NCtx where
  AddNNF 'Z     σ ('End τ)           = TypeError (Text "Cannot add " :<>: ShowType σ :<>: Text " to the context [" :<>: ShowType τ :<>: Text "]")
  AddNNF ('S x) σ ('End τ)           = 'Cons ('Just τ) (SingletonNF x σ)
  AddNNF 'Z     σ ('Cons 'Nothing g) = 'Cons ('Just σ) g
  AddNNF 'Z     σ ('Cons ('Just τ) g) = TypeError (Text "Cannot add " :<>: ShowType σ :<>: Text " to the context " :<>: ShowType τ :<>: Text "::" :<>: ShowType τ)
  AddNNF ('S x) σ ('Cons u       g)  = 'Cons u (AddNNF x σ g)

type family Remove (x :: Nat) (g :: Ctx) :: Ctx where
  Remove x 'Empty = TypeError (Text "Cannot remove anything from an empty context")
  Remove x ('N γ) = RemoveN x γ
type family RemoveN (x :: Nat) (γ :: NCtx) :: Ctx where
  RemoveN 'Z     ('End _)            = 'Empty
  RemoveN 'Z     ('Cons ('Just _) γ) = 'N ('Cons 'Nothing γ)
  RemoveN ('S x) ('Cons u γ)         = ConsN u (RemoveN x γ)

type family Merge (γ1 :: Ctx) (γ2 :: Ctx) :: Ctx where
  Merge γ1 γ2 = MaybeError (MergeF γ1 γ2) 
                           (Text "Cannot merge context " :<>: ShowType γ1 
                       :<>: Text "with context " :<>: ShowType γ2)
type family MergeN (γ1 :: NCtx) (γ2 :: NCtx) :: NCtx where
  MergeN γ1 γ2 = MaybeError (MergeNF γ1 γ2) 
                            (Text "Cannot merge non-empty context " :<>: ShowType γ1 
                        :<>: Text "with non-empty context " :<>: ShowType γ2)


type family MaybeMap (f :: a -> b) (m :: Maybe a) :: Maybe b where
  MaybeMap f (Just a) = Just (f a)
  MaybeMap f Nothing  = Nothing

type family MergeF (g1 :: Ctx) (g2 :: Ctx) :: Maybe Ctx where
  MergeF 'Empty  'Empty  = 'Just 'Empty
  MergeF 'Empty  ('N g2) = 'Just ('N g2)
  MergeF ('N g1) 'Empty  = 'Just ('N g1)
  MergeF ('N g1) ('N g2) = MaybeMap 'N (MergeNF g1 g2)
type family MergeNF (g1 :: NCtx) (g2 :: NCtx) :: Maybe NCtx where
  MergeNF ('End σ)             ('Cons 'Nothing g2)  = Just ('Cons ('Just σ) g2)
  MergeNF ('Cons 'Nothing g1)  ('End σ)             = Just ('Cons ('Just σ) g1)
  MergeNF ('Cons 'Nothing g1)  ('Cons 'Nothing g2)  = 
          MaybeMap ('Cons Nothing) (MergeNF g1 g2)
  MergeNF ('Cons ('Just σ) g1) ('Cons 'Nothing g2)  = 
          MaybeMap ('Cons ('Just σ)) (MergeNF g1 g2)
  MergeNF ('Cons 'Nothing g1)  ('Cons ('Just σ) g2) = 
          MaybeMap ('Cons ('Just σ)) (MergeNF g1 g2)
  MergeNF ('Cons ('Just _) _) ('Cons ('Just _) _) = Nothing
