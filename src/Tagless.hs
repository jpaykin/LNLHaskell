{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             InstanceSigs, TypeApplications, 
             ScopedTypeVariables, UndecidableInstances,
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
data LolliSig ty = Lolli ty ty

-- 2) embed it into LType
type (σ :: LType) ⊸ (τ :: LType) = MkLType ('Lolli σ τ)
infixr 0 ⊸

-- 3) define an LVal instance
data instance LVal m (MkLType ('Lolli (σ :: LType) (τ :: LType))) = 
    VAbs (LVal m σ -> m (LVal m τ))

-- 4) Define an interface
class HasLolli (exp :: Exp) where
  λ :: forall x (σ :: LType) (γ :: Ctx) (γ' :: Ctx) (γ'' :: Ctx) (τ :: LType).
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (exp γ'' σ -> exp γ' τ) -> exp γ (σ ⊸ τ)
  (^) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (σ :: LType) (τ :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 (σ ⊸ τ) -> exp γ2 σ -> exp γ τ



-- One -----------------------------------------------
data OneSig ty = OneSig
type One = (MkLType 'OneSig :: LType)
data instance LVal m (MkLType 'OneSig) = VUnit

class HasOne (exp :: Exp) where
  unit :: exp (Empty :: Ctx) (One :: LType)
  letUnit :: CMerge γ1 γ2 γ 
          => exp γ1 One -> exp γ2 τ -> exp γ τ


-- Tensor ---------------------------------------------  


data TensorSig ty = TensorSig ty ty
type (σ1 :: LType) ⊗ (σ2 :: LType) = MkLType ('TensorSig σ1 σ2)
data instance LVal m (MkLType ('TensorSig σ1 σ2)) = VPair (LVal m σ1) (LVal m σ2)

-- Exp = Ctx -> LType -> Type
class HasTensor (exp :: Exp) where
  (⊗) :: forall (γ1 :: Ctx) (γ2 :: Ctx) (γ :: Ctx) (τ1 :: LType) (τ2 :: LType).
         CMerge γ1 γ2 γ
      => exp γ1 τ1 -> exp γ2 τ2 -> exp γ (τ1 ⊗ τ2)
  letPair :: forall x1 x2 (σ1 :: LType) (σ2 :: LType) (τ :: LType) 
                    (γ1 :: Ctx) (γ2 :: Ctx) (γ2' :: Ctx) (γ :: Ctx) 
                    (γ2'' :: Ctx) (γ21 :: Ctx) (γ22 :: Ctx).
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

data BottomSig ty = BottomSig
type Bottom = (MkLType 'BottomSig :: LType)
data instance LVal m (MkLType 'BottomSig)

-- Additive Sum ---------------------------------------

data PlusSig ty = PlusSig ty ty
type (⊕) (σ :: LType) (τ :: LType) = MkLType ('PlusSig σ τ)
data instance LVal m (MkLType ('PlusSig σ τ)) = VLeft (LVal m σ) | VRight (LVal m τ)

class HasPlus (exp :: Exp) where
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

data WithSig ty = WithSig ty ty
type (σ :: LType) & (τ :: LType) = MkLType ('WithSig σ τ)
data instance LVal m (MkLType ('WithSig σ τ)) = VWith (LVal m σ) (LVal m τ)

class HasWith (exp :: Exp) where
  (&) :: exp γ τ1 -> exp γ τ2 -> exp γ (τ1 & τ2)
  proj1 :: exp γ (τ1 & τ2) -> exp γ τ1
  proj2 :: exp γ (τ1 & τ2) -> exp γ τ2


-- Lower ----------------------------------------------
data LowerSig ty = LowerSig Type
type Lower a = (MkLType ('LowerSig a) :: LType)
data instance LVal m (MkLType ('LowerSig a)) = VBang a

class HasLower (exp :: Exp) where
  put  :: a -> exp Empty (Lower a)
  (>!) :: CMerge γ1 γ2 γ => exp γ1 (Lower a) -> (a -> exp γ2 τ) -> exp γ τ


-- Lift --------------------------------------------------


data Lift (exp :: Exp) (τ :: LType) where
  Suspend :: exp 'Empty τ -> Lift exp τ
force :: Lift exp τ -> exp 'Empty τ
force (Suspend e) = e

---------------------------------------------------------------
-- Examples ---------------------------------------------------
---------------------------------------------------------------

{-
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
-}

--compose :: (HasLolli exp,CMerge γ1 γ2 γ)
--        => exp γ1 (τ ⊸ ρ) -> exp γ2 (σ ⊸ τ) -> exp γ (σ ⊸ ρ)
--compose g f = λ $ \x -> g ^ (f ^ x)


---------------------------------------------------------------
-- Patterns ---------------------------------------------------
---------------------------------------------------------------

class HasVar (exp :: Exp) where
  var :: forall x (σ :: LType) (γ :: Ctx). 
         CSingletonCtx x σ γ => exp γ σ

{-
data Bang a = Bang a
type family Pat (σ :: LType) where
    Pat ('LType _ ('TensorSig σ τ)) = (Pat σ, Pat τ)
    Pat ('LType _ ('PlusSig σ τ))   = Either (Pat σ) (Pat τ)
    Pat ('LType _ ('LowerSig a))    = Bang a
--  Pat _                           = 

-- FreshCtx γ σ is a context γ extended with fresh variables for every pattern variable in σ
class FreshCtx (γ :: Ctx) (σ :: LType) (γ' :: Ctx)
instance (pf ~ IsInSig TensorSig, FreshCtx γ σ1 γ0, FreshCtx γ0 σ2 γ')
      => FreshCtx (γ :: Ctx) ('LType pf ('TensorSig σ1 σ2)) γ'
-}


--type family   FreshCtx (γ :: Ctx) (σ :: LType) :: Ctx where
--    FreshCtx γ ('LType _ ('TensorSig σ τ)) = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ ('LType _ ('PlusSig σ τ))   = FreshCtx (FreshCtx γ σ) τ
--    FreshCtx γ σ                           = AddFresh γ σ

--class (Matchable' exp (Div γout γin) σ (Pat σ), CMerge γin (Div γout γin) γout) 
--    => Matchable exp γin γout σ 
--type Matchable (exp :: Exp) σ = 
--    (WFCtx (FreshCtx 'Empty σ), Matchable' exp (FreshCtx 'Empty σ) σ (Pat σ))

{-
type Matchable exp σ = Matchable' exp σ (Pat σ)
-- essentially saying that pat ≅ exp (FreshCtx Empty σ) σ
class Matchable' (exp :: Exp) σ pat where
  pat   :: FreshCtx 'Empty σ γ => pat -> exp γ σ
  λcase :: (FreshCtx γ σ γ')
        => (pat -> exp γ' τ) -> exp γ (σ ⊸ τ)
-}

-- γ0 is a context of variables not to use
-- class HasLolli exp 
--    => Matchable' (exp :: Exp) (γ :: Ctx)
--                  (σ :: LType) (pat :: Type) where
--   pat   :: pat -> exp γ σ
--   λcase :: forall γ0 γ' τ. 
--            CMerge γ γ0 γ' => (pat -> exp γ' τ) -> exp γ0 (σ ⊸ τ)

--  match :: (CMerge γ1 γ2 γ', CMerge γ γ2 γ2')
--        => exp γ1 σ -> (pat -> exp γ2' τ) -> exp γ' τ
--  match e f = λcase f ^ e

--instance ( CMerge γ1 γ2 γ, HasTensor exp
--         , Matchable' exp γ1 σ1 pat1, Matchable' exp γ2 σ2 pat2
--         , τ ~ (σ1 ⊗ σ2) )
--      => Matchable' (exp :: Exp) γ τ (pat1,pat2) where

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

--foo :: forall (exp :: Exp) σ τ. 
--       (HasTensor exp, Matchable exp σ, Matchable exp τ)
--    => Lift exp (σ ⊗ τ ⊸ τ ⊗ σ)
--foo = Suspend . λcase $ \(x,y) -> pat y ⊗ pat x
