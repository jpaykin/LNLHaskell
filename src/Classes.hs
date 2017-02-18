{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, FlexibleContexts, UndecidableInstances
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors 
                               -fno-warn-redundant-constraints #-}

module Classes where

import Prelude hiding (div)

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

class (γ' ~ Add x σ γ, γ ~ Remove x γ')
   => CAddCtx (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: Ctx) 
    | x σ γ -> γ', x γ' -> σ γ
  where
    add    :: forall m. LVal m σ -> SCtx m γ -> SCtx m γ'
--    remove :: SCtx γ' -> (LVal σ, SCtx γ)
instance CAddCtxN x (σ :: LType) (γ :: Ctx) (γ' :: NCtx) (CountN γ')
      => CAddCtx x σ γ ('N γ') 
  where
    add v g = SN $ addN @x v g

class (γ' ~ AddN x σ γ, γ ~ RemoveN x γ')
   => CAddCtxN (x :: Nat) (σ :: LType) (γ :: Ctx) (γ' :: NCtx) (len :: Nat)
    | x σ γ -> len γ', x γ' len -> σ γ 
  where
    addN    :: forall m. LVal m σ -> SCtx m γ -> SNCtx m γ'


instance CSingletonNCtx x (σ :: LType) (γ' :: NCtx)
      => CAddCtxN x σ Empty γ' (S Z)
  where
    addN s SEmpty = singletonN @x s
instance CSingletonNCtx x σ γ'
      => CAddCtxN (S x) σ (N (End τ)) (Cons (Just τ) γ') (S (S Z))
  where
    addN s (SN (SEnd t)) = SCons (SJust t) $ singletonN @x s
instance CAddCtxN x (σ :: LType) (N (γ :: NCtx)) (γ' :: NCtx) (S (S n))
      => CAddCtxN (S x) σ (N (Cons Nothing γ)) (Cons Nothing γ') (S (S n))
  where
    addN s (SN (SCons _ g)) = SCons SNothing (addN @x s (SN g))
instance CAddCtxN x (σ :: LType) (N (γ :: NCtx)) (γ' :: NCtx) (S (S n)) 
      => CAddCtxN (S x) σ (N (Cons (Just τ) γ)) (Cons (Just τ) γ') (S (S (S n)))
  where
    addN s (SN (SCons u g)) = SCons u $ addN @x s (SN g)

---------------------

-- outputs the number of variables used in the NCtx
type family CountN g :: Nat where
  CountN ('End _)            = 'S 'Z
  CountN ('Cons ('Just _) g) = 'S (CountN g)
  CountN ('Cons 'Nothing g)   = CountN g

type family IsSingleton  g :: Bool where
  IsSingleton ('End σ)            = 'True
  IsSingleton ('Cons ('Just _) _) = 'False
  IsSingleton ('Cons 'Nothing   g) = IsSingleton g

type family IsDouble g :: Bool where
  IsDouble ('End σ) = 'False
  IsDouble ('Cons ('Just _) g) = IsSingleton g
  IsDouble ('Cons 'Nothing g)   = IsDouble g

class CIsSingleton (g :: NCtx) (flag :: Bool) | g -> flag where

instance CIsSingleton ('End σ) 'True where
instance CIsSingleton ('Cons ('Just σ) g) 'False where
instance CIsSingleton g b => CIsSingleton ('Cons 'Nothing g) b where

-- Singleton Context ------------------------------------------

class (g ~ Singleton x σ, Remove x g ~ Empty)
   => CSingletonCtx (x :: Nat) (σ :: LType) (g :: Ctx) 
      | x σ -> g, g -> x σ where
  singleton :: LVal m σ -> SCtx m g
  singletonInv :: SCtx m g -> LVal m σ
class (g ~ SingletonN x σ, RemoveN x g ~ Empty)
   => CSingletonNCtx (x :: Nat) (σ :: LType) (g :: NCtx) 
    | x σ -> g, g -> x σ where
  singletonN :: LVal m σ -> SNCtx m g
  singletonNInv :: SNCtx m g -> LVal m σ

instance CSingletonNCtx 'Z σ ('End σ) where
  singletonN v = SEnd v
  singletonNInv (SEnd v) = v
instance CSingletonNCtx x σ g => CSingletonNCtx ('S x) σ ('Cons 'Nothing g) where
  singletonN v = SCons SNothing $ singletonN @x v
  singletonNInv (SCons _ g) = singletonNInv @x g

instance CSingletonNCtx x σ g => CSingletonCtx x σ ('N g) where
  singleton v = SN $ singletonN @x v
  singletonInv (SN g) = singletonNInv @x g

-- Well-formed contexts --------------------------------

class (CDiv γ 'Empty γ, CDiv  γ γ 'Empty, CMergeForward 'Empty γ γ, CMergeForward γ 'Empty γ) 
    => WFCtx γ 
class (CDivN γ γ 'Empty) => WFNCtx γ

instance WFCtx 'Empty
instance WFNCtx γ => WFCtx ('N γ)
instance WFNCtx ('End σ)
instance WFNCtx γ => WFNCtx ('Cons 'Nothing γ)
instance WFNCtx γ => WFNCtx ('Cons ('Just σ) γ)

-- Merge ----------------------------------------------------


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
--  split = split'  @g1 @g2 @g3

class CMergeForward (g1 :: Ctx) (g2 :: Ctx) (g3 :: Ctx) | g1 g2 -> g3 where
  split :: SCtx m g3 -> (SCtx m g1, SCtx m g2)
class CMergeNForward g1 g2 g3 | g1 g2 -> g3 where
  splitN :: SNCtx m g3 -> (SNCtx m g1, SNCtx m g2)

instance CMergeForward ('Empty :: Ctx) ('Empty :: Ctx) ('Empty :: Ctx) where
  split _ = (SEmpty,SEmpty)
instance CMergeForward 'Empty ('N g) ('N g) where
  split g = (SEmpty,g)
instance CMergeForward ('N g) 'Empty ('N g) where
  split g = (g,SEmpty)
instance CMergeNForward g1 g2 g3 => CMergeForward ('N g1) ('N g2) ('N g3) where
  split (SN g) = let (g1,g2) = splitN g
                 in (SN g1, SN g2)

instance CMergeNForward ('End σ) ('Cons 'Nothing g2) ('Cons ('Just σ) g2) where
  splitN (SCons (SJust v) g) = (SEnd v, SCons SNothing g)
instance CMergeNForward ('Cons 'Nothing g1) ('End σ) ('Cons ('Just σ) g1) where
  splitN (SCons (SJust v) g) = (SCons SNothing g, SEnd v)
-- u1=Nothing, u2=Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons 'Nothing g2) ('Cons 'Nothing g3) 
  where
    splitN (SCons SNothing g) = (SCons SNothing g1, SCons SNothing g2)
      where
        (g1,g2) = splitN g
-- u1=Just σ, u2= Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons ('Just σ) g1) ('Cons 'Nothing g2) ('Cons ('Just σ) g3) 
  where
    splitN (SCons (SJust v) g) = (SCons (SJust v) g1, SCons SNothing g2)
      where
        (g1,g2) = splitN g
-- u1=Nothing, u2= Just σ
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons ('Just σ) g2) ('Cons ('Just σ) g3) 
  where
    splitN (SCons (SJust v) g) = (SCons SNothing g1, SCons (SJust v) g2) 
      where
        (g1,g2) = splitN g




-- Div ---------------------------------------

class CDiv (g1 :: Ctx) (g2 :: Ctx) (g3 :: Ctx) | g1 g2 -> g3 where
--  split' :: SCtx m g1 -> (SCtx m g2, SCtx m g3)

instance CDiv ('Empty :: Ctx) ('Empty :: Ctx) ('Empty :: Ctx) where
--  split' () = ((),())
instance CDiv ('N g) 'Empty ('N g) where
--  split' g = ((),g)
instance CDivN g1 g2 g3 => CDiv ('N g1) ('N g2) g3 where
--  split' = splitN @g1 @g2 @g3

class CDivN (g1 :: NCtx) (g2 :: NCtx) (g3 :: Ctx) | g1 g2 -> g3 where
--  splitN :: SNCtx m g1 -> (SNCtx m g2, SCtx m g3)

instance σ ~ τ => CDivN ('End σ :: NCtx) ('End τ) ('Empty :: Ctx) where
--  splitN g = (g,())
instance CDivN ('Cons ('Just σ) g) ('End σ) ('N ('Cons 'Nothing g)) where
--  splitN (s,g) = (s,g)
instance (CMergeU u3 u2 u1, CDivN g1 g2 g3, g3' ~ ConsN u3 g3)
      => CDivN ('Cons u1 g1) ('Cons u2 g2) g3' where





