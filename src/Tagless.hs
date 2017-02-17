{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, ConstraintKinds,
             TypeFamilyDependencies, LambdaCase
#-}

module Tagless where
 
import Prelude hiding ((^), uncurry)
import Prelim hiding (One)
import Types
import Classes

import Data.Kind


-- For each domain:

-- 1) Declare a data type
data LolliSig sig = Lolli (LType sig) (LType sig)

-- 2) embed it into LType
type (σ :: LType sig) ⊸ τ = MkLType sig ('Lolli σ τ)
infixr 0 ⊸

-- 3) define an LVal instance
type instance LVal ('LType _ ('Lolli σ τ) :: LType sig) = LVal σ -> SigEffect sig (LVal τ)

-- 4) Define an interface
class HasLolli (exp :: Exp sig) where
  λ :: (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (exp γ'' σ -> exp γ' τ) -> exp γ (σ ⊸ τ)
  (^) :: CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ) -> exp γ2 σ -> exp γ τ




-- One -----------------------------------------------
data OneSig ty = OneSig
type One = (MkLType sig 'OneSig :: LType sig)
type instance LVal ('LType _ 'OneSig) = ()

class HasOne (exp :: Exp sig) where
  unit :: exp Empty One
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ



-- Tensor ---------------------------------------------  

data TensorSig sig = TensorSig (LType sig) (LType sig)
type (σ1 :: LType sig) ⊗ (σ2 :: LType sig) = MkLType sig ('TensorSig σ1 σ2)
type instance LVal ('LType _ ('TensorSig σ1 σ2) :: LType sig) = (LVal σ1, LVal σ2)

class HasTensor (exp :: Exp sig) where
  (⊗) :: CMerge γ1 γ2 γ
      => exp γ1 τ1 -> exp γ2 τ2 -> exp γ (τ1 ⊗ τ2)
  letPair :: forall x1 x2 (σ1 :: LType sig) σ2 τ γ1 γ2 γ γ2' γ2'' γ21 γ22.
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ, x2 ~ Fresh2 γ )
      => exp γ1 (σ1 ⊗ σ2)
      -> ((exp γ21 σ1, exp γ22 σ2) -> exp γ2'' τ)
      -> exp γ τ


-- Bottom -------------------------------------------

data BottomSig sig = BottomSig
type Bottom = (MkLType sig 'BottomSig :: LType sig)
data Void
type instance LVal ('LType _ 'BottomSig) = Void

-- Additive Sum ---------------------------------------

data PlusSig sig = PlusSig (LType sig) (LType sig)
type (⊕) (σ :: LType sig) (τ :: LType sig) = MkLType sig ('PlusSig σ τ)
type instance LVal ('LType _ ('PlusSig σ τ)) = Either (LVal σ) (LVal τ)

class HasPlus (exp :: Exp sig) where
  inl :: exp γ τ1 -> exp γ (τ1 ⊕ τ2)
  inr :: exp γ τ2 -> exp γ (τ1 ⊕ τ2)
  caseof :: ( CAddCtx x σ1 γ2 γ21, CSingletonCtx x σ1 γ21'
            , CAddCtx x σ2 γ2 γ22, CSingletonCtx x σ2 γ22'
            , x ~ Fresh γ
            , CMerge γ1 γ2 γ )
        => exp γ1 (σ1 ⊕ σ2)
        -> (exp γ21' σ1 -> exp γ21 τ)
        -> (exp γ22' σ2 -> exp γ22 τ)
        -> exp γ τ




-- Additive Product -------------------------------------

data WithSig sig = WithSig (LType sig) (LType sig)
type (σ :: LType sig) & (τ :: LType sig) = MkLType sig ('WithSig σ τ)
type instance LVal ('LType _ ('WithSig σ τ)) = (LVal σ, LVal τ)

class HasWith (exp :: Exp sig) where
  (&) :: exp γ τ1 -> exp γ τ2 -> exp γ (τ1 & τ2)
  proj1 :: exp γ (τ1 & τ2) -> exp γ τ1
  proj2 :: exp γ (τ1 & τ2) -> exp γ τ2


-- Lower ----------------------------------------------
data LowerSig sig = LowerSig Type
type Lower a = (MkLType sig ('LowerSig a) :: LType sig)
type instance LVal ('LType _ ('LowerSig a)) = a

class HasLower (exp :: Exp sig) where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ


-- Lift --------------------------------------------------


data Lift (exp :: Exp sig) (τ :: LType sig) where
  Suspend :: exp 'Empty τ -> Lift exp τ
force :: Lift exp τ -> exp 'Empty τ
force (Suspend e) = e


---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

id :: HasLolli exp => Lift exp (σ ⊸ σ)
id = Suspend . λ $ \x -> x

sApp :: HasLolli exp => Lift exp (σ ⊸ τ) -> Lift exp σ -> Lift exp τ
sApp f e = Suspend $ force  f ^ force e

uncurryL :: (HasLolli exp,HasTensor exp) => Lift exp ((σ1 ⊸ σ2 ⊸ τ) ⊸ σ1 ⊗ σ2 ⊸ τ)
uncurryL = Suspend . λ $ \f -> λ $ \x -> 
    x `letPair` \(x1,x2) -> 
    f ^ x1 ^ x2
uncurry :: (HasLolli exp,HasTensor exp,WFCtx γ) => exp γ (σ1 ⊸ σ2 ⊸ τ) -> exp γ (σ1 ⊗ σ2 ⊸ τ)
uncurry e = force uncurryL ^ e

--compose :: (HasLolli exp,CMerge γ1 γ2 γ)
--        => exp γ1 (τ ⊸ ρ) -> exp γ2 (σ ⊸ τ) -> exp γ (σ ⊸ ρ)
--compose g f = λ $ \x -> g ^ (f ^ x)


---------------------------------------------------------------
-- Patterns ---------------------------------------------------
---------------------------------------------------------------

class HasVar (exp :: Exp sig) where
  var :: forall x σ γ. CSingletonCtx x σ γ => exp γ σ

data Bang a = Bang a
type family Pat (σ :: LType sig) where
    Pat ('LType _ ('TensorSig σ τ)) = (Pat σ, Pat τ)
    Pat ('LType _ ('PlusSig σ τ))   = Either (Pat σ) (Pat τ)
    Pat ('LType _ ('LowerSig a))    = Bang a
--  Pat _                           = 

-- FreshCtx γ σ is a context γ extended with fresh variables for every pattern variable in σ
class FreshCtx (γ :: Ctx sig) (σ :: LType sig) (γ' :: Ctx sig)
instance (pf ~ IsInSig TensorSig sig, FreshCtx γ σ1 γ0, FreshCtx γ0 σ2 γ')
      => FreshCtx (γ :: Ctx sig) ('LType pf ('TensorSig σ1 σ2)) γ'

--type family   FreshCtx (γ :: Ctx sig) (σ :: LType sig) :: Ctx sig where
--    FreshCtx γ ('LType _ ('TensorSig σ τ)) = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ ('LType _ ('PlusSig σ τ))   = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ σ                           = AddFresh γ σ

--class (Matchable' exp (Div γout γin) σ (Pat σ), CMerge γin (Div γout γin) γout) 
--    => Matchable exp γin γout σ 
--type Matchable (exp :: Exp sig) σ = 
--    (WFCtx (FreshCtx 'Empty σ), Matchable' exp (FreshCtx 'Empty σ) σ (Pat σ))

type Matchable exp σ = Matchable' exp σ (Pat σ)
-- essentially saying that pat ≅ exp (FreshCtx Empty σ) σ
class Matchable' (exp :: Exp sig) σ pat where
  pat   :: FreshCtx 'Empty σ γ => pat -> exp γ σ
  λcase :: (FreshCtx γ σ γ')
        => (pat -> exp γ' τ) -> exp γ (σ ⊸ τ)


-- γ0 is a context of variables not to use
-- class HasLolli exp 
--    => Matchable' (exp :: Exp sig) (γ :: Ctx sig)
--                  (σ :: LType sig) (pat :: Type) where
--   pat   :: pat -> exp γ σ
--   λcase :: forall γ0 γ' τ. 
--            CMerge γ γ0 γ' => (pat -> exp γ' τ) -> exp γ0 (σ ⊸ τ)

--  match :: (CMerge γ1 γ2 γ', CMerge γ γ2 γ2')
--        => exp γ1 σ -> (pat -> exp γ2' τ) -> exp γ' τ
--  match e f = λcase f ^ e

--instance ( CMerge γ1 γ2 γ, HasTensor exp
--         , Matchable' exp γ1 σ1 pat1, Matchable' exp γ2 σ2 pat2
--         , τ ~ (σ1 ⊗ σ2) )
--      => Matchable' (exp :: Exp sig) γ τ (pat1,pat2) where

--   pat (p1,p2) = (pat @_ @_ @γ1 @σ1 p1) ⊗ (pat @_ @_ @γ2 @σ2 p2)

--   λcase :: forall γ0 γ' ρ.
--            CMerge γ0 γ γ' => ((pat1,pat2) -> exp γ' ρ) -> exp γ0 (σ1 ⊗ σ2 ⊸ ρ)
--   λcase f = uncurry f'
 --    uncurry @exp $ λcase (\p1 -> λcase @_ @exp (\p2 -> f (p1,p2)))
--     where
---       f' :: exp γ0 (σ1 ⊸ σ2 ⊸ ρ)
--       f' = undefined -- λcase @_ @exp @γ1 @σ1 @pat1 $ \p1 -> _
    

--  match :: forall γ1 γ2 γ' γ2' τ. (CMerge γ1 γ2 γ', CMerge γ γ2 γ2')
--        => exp γ1 (σ1 ⊗ σ2) -> ((pat1,pat2) -> exp γ2' τ) -> exp γ' τ
--  match = undefined
--  match e f   = letPair @_ @_ @_ @_ @_ @_ @_ @γ1 e $ \(x1,x2) ->
--                match @_ @exp x1 $ \p1 ->
--                match @_ @exp x2 $ \p2 ->
--                f (p1,p2)


--instance (HasPlus exp, Matchable' exp γ σ1 pat1, Matchable' exp γ σ2 pat2, τ ~ (σ1 ⊕ σ2))
--      => Matchable' exp γ τ (Either pat1 pat2) where
--  pat (Left  p) = inl $ pat p
--  pat (Right p) = inr $ pat p

-- Example programs

--foo :: forall sig (exp :: Exp sig) σ τ. 
--       (HasTensor exp, Matchable exp σ, Matchable exp τ)
--    => Lift exp (σ ⊗ τ ⊸ τ ⊗ σ)
--foo = Suspend . λcase $ \(x,y) -> pat y ⊗ pat x
