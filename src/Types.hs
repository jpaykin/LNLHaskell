module Types where

import Prelim

import Data.Kind
import GHC.TypeLits hiding (Div)
import Data.Proxy
--import Data.Singletons
--import Data.Constraint
import Unsafe.Coerce
import Prelude hiding (lookup)
import qualified Data.IntMap.Strict as M
--import qualified Data.IntSet as S
--import Debug.Trace

data LType where MkLType :: ty LType -> LType
  -- ty :: * -> *

type Sig = Ctx -> LType -> Type
type Val = LType -> Type

data family LVal (sig :: Sig) :: Val
type family Effect (sig :: Sig) :: Type -> Type

type Ctx = [(Nat,LType)]


-------------------------
-- Evaluation contexts --
-------------------------

data EVal sig where
  EVal :: !(LVal sig σ) -> EVal sig

unsafeEValCoerce :: forall σ sig. EVal sig -> LVal sig σ
unsafeEValCoerce (EVal v) = unsafeCoerce v

newtype ECtx sig γ = ECtx (M.IntMap (EVal sig))

eEmpty :: ECtx sig '[]
eEmpty = ECtx M.empty

eCons :: forall x σ γ sig. KnownNat x 
      => LVal sig σ -> ECtx sig γ -> ECtx sig ('(x,σ) ': γ)
eCons v (ECtx γ) = ECtx (M.insert (knownInt @x) (EVal v) γ)


knownInt :: forall n. KnownNat n => Int
knownInt = fromIntegral $ natVal (Proxy :: Proxy n)

unsafeLookupECtx :: forall x σ γ sig. 
                KnownNat x 
             => ECtx sig γ -> LVal sig σ
unsafeLookupECtx (ECtx γ) = unsafeEValCoerce $ γ M.! knownInt @x

lookupECtx :: forall x σ γ sig. (KnownNat x, Lookup γ x ~ 'Just σ)
           => ECtx sig γ -> LVal sig σ
lookupECtx = unsafeLookupECtx @x
--lookupECtx (ECtx γ) = unsafeCoerce $ γ ! knownInt @x

lookupSingleton :: forall x σ sig. KnownNat x
                => ECtx sig '[ '(x,σ) ] -> LVal sig σ
lookupSingleton γ = unsafeLookupECtx @x γ


addECtx :: forall σ x γ sig proxy. KnownNat x 
        => proxy x -> LVal sig σ -> ECtx sig γ -> ECtx sig (AddF x σ γ)
addECtx _ v (ECtx γ) = ECtx $ M.insert (knownInt @x) (EVal v) γ


splitECtx :: forall γ1 γ2 γ sig. (γ ~ MergeF γ1 γ2)
          => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
splitECtx (ECtx γ) = (ECtx γ, ECtx γ)


-- Fresh variables ------------------------------------------

type family Fresh (γ :: Ctx) :: Nat where
  Fresh '[] = 0
  Fresh '[ '(x,_) ] = x+1
  Fresh (_ ': γ)    = Fresh γ -- since contexts are ordered

-- Type families

type family Lookup (γ :: Ctx) (x :: Nat) :: Maybe LType where
  Lookup '[] _        = 'Nothing
  Lookup ('(y,σ):γ) x = If (x ==? y) ('Just σ) (Lookup γ x)
  
type family Remove (x :: Nat) (γ :: Ctx) :: Ctx where
  Remove x '[]           = TypeError ('Text "Error in Remove")
  Remove x ('(y,σ) ': γ) = CompareOrd (CmpNat x y)
                                      (TypeError ('Text "Error in Remove")) -- x < y
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
                                      (TypeError ('Text "Error in AddF")) -- x == y
                                      ('(y,τ) ': AddF x σ γ) -- x > y


--If (x ==? y) (TypeError (Text "Error in AddF")) 
--                                        ('(y,τ) ': AddF x σ γ)

type family MergeF (γ1 :: Ctx) (γ2 :: Ctx) :: Ctx where
  MergeF '[] γ2 = γ2
--  MergeF ('(x,σ) ': γ1) γ2 = MergeF γ1 (AddF x σ γ2)
  MergeF ('(x,σ) ': γ1) γ2 = AddF x σ (MergeF γ1 γ2)
