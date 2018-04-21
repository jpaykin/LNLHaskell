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
--import Data.Singletons
--import Data.Constraint
import Unsafe.Coerce
import Prelude hiding (lookup)
import qualified Data.IntMap as M
import qualified Data.IntSet as S

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


data EVal sig where
  EVal :: !(LVal sig σ) -> EVal sig

unsafeEValCoerce :: forall σ sig. EVal sig -> LVal sig σ
unsafeEValCoerce (EVal v) = unsafeCoerce v

newtype ECtx sig γ = ECtx (M.IntMap (EVal sig))


eRemove :: Int -> ECtx sig γ -> ECtx sig γ'
eRemove x (ECtx γ) = ECtx $ M.delete x γ

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

lookupSingleton :: forall x σ sig. KnownNat x
                => ECtx sig '[ '(x,σ) ] -> LVal sig σ
lookupSingleton γ = unsafeLookupECtx @x γ


addECtx :: forall σ x γ sig proxy. KnownNat x 
        => proxy x -> LVal sig σ -> ECtx sig γ -> ECtx sig (AddF x σ γ)
addECtx _ v (ECtx γ) = ECtx $ M.insert (knownInt @x) (EVal v) γ

removeECtx :: forall x σ γ sig. 
              KnownNat x 
           => ECtx sig (AddF x σ γ) -> (LVal sig σ, ECtx sig γ)
removeECtx γ = (unsafeLookupECtx @x γ, eRemove x γ)
  where x = knownInt @x

class KnownDomain (γ :: Ctx) where
  domain :: S.IntSet

instance KnownDomain '[] where
  domain = S.empty
instance (KnownNat x, KnownDomain γ) => KnownDomain ('(x,σ) ': γ) where
  domain = S.insert x $ domain @γ
    where x = knownInt @x

splitECtx :: forall γ1 γ2 γ sig. (KnownDomain γ1, γ ~ MergeF γ1 γ2)
          => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
splitECtx (ECtx γ) = let (γ1',γ2') = M.partitionWithKey (\x _ -> S.member x γ1) γ
                     in (ECtx γ1', ECtx γ2')
  where γ1 = domain @γ1

{-
class γ ~ MergeF γ1 γ2 => CMergeF γ1 γ2 γ where
  splitECtx :: ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)

instance CMergeF '[] γ2 γ2 where
  splitECtx γ2 = (eEmpty,γ2)

instance (CMergeF γ1 γ2 γ0, γ ~ AddF x σ γ0, KnownNat x) 
       => CMergeF ('(x,σ) ': γ1) γ2 γ where
  splitECtx γ = let (v,γ')  = removeECtx @x @σ γ
                    (γ1,γ2) = splitECtx @γ1 @γ2 γ' 
                in (eCons @x v γ1, γ2)
-}


{-
data ECtx sig γ where
  EEmpty :: ECtx sig '[]
  ECons :: KnownNat x 
        => proxy x -> LVal sig σ -> ECtx sig γ -> ECtx sig ('(x,σ) ': γ)

lookupHead :: CmpNat x y ~ 'EQ
           => proxy x -> proxy' y -> Dict (Lookup ('(y,σ) ': γ) x ~ 'Just σ)
lookupHead _ _ = unsafeCoerce (Dict :: Dict ())

lookupTail :: (x ==? y) ~ 'False
           => proxy x -> proxy' y -> Dict (Lookup ('(y,σ) ': γ) x ~ Lookup γ x)
lookupTail _ _ = unsafeCoerce (Dict :: Dict ())

lookupECtx :: KnownNat x
       => Dict (Lookup γ x ~ 'Just σ) -> proxy x -> ECtx sig γ -> LVal sig σ
lookupECtx d _ EEmpty        = case d of
lookupECtx  Dict x (ECons y (v :: LVal sig τ) γ) = case cmpNat x y of
    CLT Dict -> case lookupTail x y of Dict -> lookupECtx Dict x γ
    CEQ Dict -> v
    CGT Dict -> case lookupTail x y of Dict -> lookupECtx Dict x γ
-}

{-
unsafeLookupECtx :: KnownNat x
       => proxy x -> ECtx sig γ -> LVal sig σ
unsafeLookupECtx = lookupECtx (unsafeCoerce (Dict :: Dict ()))
-}

{-
mergeEmpty :: '[] ~ MergeF γ1 γ2 => Dict (γ1 ~ '[], γ2 ~ '[])
mergeEmpty = unsafeCoerce (Dict :: Dict ((),()))
-}



--splitECtx (ECons x v γ) = (_,_)


{-

unsafeLookupECtx :: forall x σ sig γ proxy. 
              (KnownNat x) --, Lookup γ x ~ 'Just σ) 
           => proxy x → ECtx sig γ → LVal sig σ
unsafeLookupECtx x γ = unsafeEvalCoerce $ γ ! knownInt x

--inDomain :: (KnownDomain γ) => Int -> Bool
--inDomain = undefined

add :: forall σ γ x sig proxy. KnownNat x
    => proxy x -> LVal sig σ -> ECtx sig γ -> ECtx sig (AddF x σ γ)
add x v γ = insert (knownInt x) (EVal v) γ

split :: forall γ1 γ2 γ sig. (γ ~ MergeF γ1 γ2)
      => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
split γ = foldrWithKey _ (eEmpty,eEmpty) γ
-}

{-
class γ' ~ AddF x σ γ  => CAddF x σ γ γ' where
  removeECtx :: proxy x -> ECtx sig γ' -> ECtx sig γ
instance CAddF x σ '[] '[ '(x,σ) ] where
  removeECtx _ _ = eEmpty
instance CmpNat x y ~ 'LT => CAddF x σ ('(y,τ) ': γ) ('(x,σ) ': '(y,τ) ': γ) where
  removeECtx x γ' = 


class (γ ~ MergeF γ1 γ2) => CMergeF γ1 γ2 γ where
  split :: ECtx sig γ → (ECtx sig γ1, ECtx sig γ2)

instance CMergeF '[] γ2 γ2 where
  split γ = (eEmpty, γ)
--instance CMergeF γ1 (AddF x σ γ2) γ => CMergeF ('(x,σ) ': γ1) γ2 γ where
--  split γ = splitAdd γ

--split :: forall γ1 γ2 γ sig. (γ ~ MergeF γ1 γ2, KnownDomain γ1)
--       => ECtx sig γ -> (ECtx sig γ1, ECtx sig γ2)
--split γ = partitionWithKey (\ x _ -> inDomain @γ1 x) γ
-}

{-
split (ECtx f) = (ECtx $ \Dict x -> f (lookupMerge1 @γ1 @γ2 @γ x) x
                 ,ECtx $ \Dict x -> f (lookupMerge2 @γ1 @γ2 @γ x) x)
-}

{-
add x v (ECtx f) = ECtx $ \Dict y ->
    case eqSNat x y of
      Left  Dict -> v -- x = y
      Right Dict -> case addLookupNEq @x @σ @γ @γ' x y of Dict -> f Dict y
-}

{-
data ECtx sig (γ :: Ctx) where
  ECtx :: (forall x σ. KnownNat x => 
                       Dict (Lookup γ x ~ Just σ) -> Proxy x -> LVal sig σ) 
       -> ECtx sig γ

eEmpty :: ECtx sig '[]
eEmpty = ECtx (\d x -> case d of)


data ECtx' sig γ where
  ENil  :: ECtx' sig '[]
  ECons :: Sing x -> LVal sig σ → ECtx' sig γ → ECtx' sig ('(x,σ) ': γ)





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
