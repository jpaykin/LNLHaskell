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

class CIn  (x :: Nat) (σ :: LType sig) (g :: Ctx sig)
class CInN (x :: Nat) (σ :: LType sig) (g :: NCtx sig)

instance CInN 'Z σ ('End σ)
instance CInN 'Z σ ('Cons ('Just σ) g)
instance (CInN x σ g) => CInN ('S x) σ ('Cons u g)

instance CInN x σ g => CIn x σ ('N g)
  

-- Add To Context ----------------------------------------------

class CAddCtx (x :: Nat) (σ :: LType sig) (γ :: Ctx sig) (γ' :: Ctx sig) | x σ γ -> γ', x γ' -> σ γ
  where
    add    :: LVal σ -> CtxVal γ -> CtxVal γ'
--    remove :: CtxVal γ' -> (LVal σ, CtxVal γ)
instance CAddCtxN x (σ :: LType sig) (γ :: Ctx sig) (γ' :: NCtx sig) (CountN γ')
      => CAddCtx x σ γ ('N γ') 
  where
    add    = addN @sig @x @σ @γ @γ' @(CountN γ')
--    remove = removeN @sig @x @σ @γ @γ' @(CountN γ')

class CAddCtxN (x :: Nat) (σ :: LType sig) (γ :: Ctx sig) (γ' :: NCtx sig) (len :: Nat)
    | x σ γ -> len γ', x γ' len -> σ γ 
  where
    addN    :: LVal σ -> CtxVal γ -> NCtxVal γ'
--    remove :: CtxVal γ' -> (LVal σ, NCtxVal γ)


instance CSingletonNCtx x (σ :: LType sig) (γ' :: NCtx sig)
      => CAddCtxN x σ Empty γ' (S Z)
  where
    addN v () = v
instance CSingletonNCtx x σ γ'
      => CAddCtxN x σ (N (End τ)) (Cons (Just τ) γ') (S (S Z))
  where
    addN v t = (t,v)
instance CAddCtxN x (σ :: LType sig) (N (γ :: NCtx sig)) (γ' :: NCtx sig) (S (S n)) 
      => CAddCtxN x σ (N (Cons Nothing γ)) (Cons Nothing γ') (S (S (S n)))
  where
    addN v g = addN @sig @x @σ @(N γ) @γ' @(S (S n)) v g
instance CAddCtxN x (σ :: LType sig) (N (γ :: NCtx sig)) (γ' :: NCtx sig) (S (S n)) 
      => CAddCtxN x σ (N (Cons (Just τ) γ)) (Cons (Just τ) γ') (S (S (S n)))
  where
    addN v (t,g) = (t,addN @sig @x @σ @(N γ) @γ' @(S (S n)) v g)

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

class CIsSingleton (g :: NCtx sig) (flag :: Bool) | g -> flag where

instance CIsSingleton ('End σ) 'True where
instance CIsSingleton ('Cons ('Just σ) g) 'False where
instance CIsSingleton g b => CIsSingleton ('Cons 'Nothing g) b where

-- Singleton Context ------------------------------------------

class LVal σ ~ CtxVal g => CSingletonCtx (x :: Nat) (σ :: LType sig) (g :: Ctx sig) 
      | x σ -> g, g -> x σ where
--  singleton :: LVal σ -> CtxVal g
--  singletonInv :: CtxVal g -> LVal σ
class LVal σ ~ NCtxVal g => CSingletonNCtx (x :: Nat) (σ :: LType sig) (g :: NCtx sig) 
    | x σ -> g, g -> x σ where
--  singletonN :: LVal σ -> NCtxVal g
--  singletonNInv :: NCtxVal g -> LVal σ

instance CSingletonNCtx 'Z σ ('End σ) where
--  singletonN = id
--  singletonNInv = id
instance CSingletonNCtx x σ g => CSingletonNCtx ('S x) σ ('Cons 'Nothing g) where
--  singletonN = singletonN @sig @x @σ @g 
--  singletonNInv = singletonNInv @sig @x @σ @g

instance CSingletonNCtx x σ g => CSingletonCtx x σ ('N g) where
--  singleton = singletonN @sig @x @σ
--  singletonInv = singletonNInv @sig @x @σ

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
--  mergeU :: MergeU u1 u2 u3

instance CMergeU (Nothing :: Maybe α) (Nothing :: Maybe α) (Nothing :: Maybe α)
--  mergeU = MergeUn
instance CMergeU (Just a) (Nothing :: Maybe α) ('Just a :: Maybe α) where
--  mergeU = MergeUL
instance CMergeU ('Nothing :: Maybe α) ('Just a) ('Just a :: Maybe α) where
--  mergeU = MergeUR

class (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2
      , WFCtx g1, WFCtx g2, WFCtx g3) 
    => CMerge g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1

instance (CMergeForward g1 g2 g3, CMergeForward g2 g1 g3, CDiv g3 g2 g1, CDiv g3 g1 g2
         , WFCtx g1, WFCtx g2, WFCtx g3)
    => CMerge g1 g2 g3 where
--  split = split'  @g1 @g2 @g3

class CMergeForward (g1 :: Ctx sig) (g2 :: Ctx sig) (g3 :: Ctx sig) | g1 g2 -> g3 where
  split :: CtxVal g3 -> (CtxVal g1, CtxVal g2)
class CMergeNForward g1 g2 g3 | g1 g2 -> g3 where
  splitN :: NCtxVal g3 -> (NCtxVal g1, NCtxVal g2)

instance CMergeForward ('Empty :: Ctx sig) ('Empty :: Ctx sig) ('Empty :: Ctx sig) where
  split () = ((),())
instance CMergeForward 'Empty ('N g) ('N g) where
  split g = ((),g)
instance CMergeForward ('N g) 'Empty ('N g) where
  split g = (g,())
instance CMergeNForward g1 g2 g3 => CMergeForward ('N g1) ('N g2) ('N g3) where
  split = splitN @g1 @g2

instance CMergeNForward ('End σ) ('Cons 'Nothing g2) ('Cons ('Just σ) g2) where
  splitN (s,g) = (s,g)
instance CMergeNForward ('Cons 'Nothing g1) ('End σ) ('Cons ('Just σ) g1) where
  splitN (s,g) = (g,s)
--instance (CMergeU u1 u2 u3, CMergeNForward g1 g2 g3)
--      => CMergeNForward ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3) where
-- u1=Nothing, u2=Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons 'Nothing g2) ('Cons 'Nothing g3) where
  splitN g = splitN @g1 @g2 g
-- u1=Just σ, u2= Nothing
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons ('Just σ) g1) ('Cons 'Nothing g2) ('Cons ('Just σ) g3) where
  splitN (s,g) = let (g1,g2) = splitN @g1 @g2 g
                 in ((s,g1),g2)
-- u1=Nothing, u2= Just σ
instance CMergeNForward g1 g2 g3
    => CMergeNForward ('Cons 'Nothing g1) ('Cons ('Just σ) g2) ('Cons ('Just σ) g3) where
  splitN (s,g) = let (g1,g2) = splitN @g1 @g2 g
                 in (g1,(s,g2))




-- Div ---------------------------------------

class CDiv (g1 :: Ctx sig) (g2 :: Ctx sig) (g3 :: Ctx sig) | g1 g2 -> g3 where
--  split' :: CtxVal g1 -> (CtxVal g2, CtxVal g3)

instance CDiv ('Empty :: Ctx sig) ('Empty :: Ctx sig) ('Empty :: Ctx sig) where
--  split' () = ((),())
instance CDiv ('N g) 'Empty ('N g) where
--  split' g = ((),g)
instance CDivN g1 g2 g3 => CDiv ('N g1) ('N g2) g3 where
--  split' = splitN @g1 @g2 @g3

class CDivN (g1 :: NCtx sig) (g2 :: NCtx sig) (g3 :: Ctx sig) | g1 g2 -> g3 where
--  splitN :: NCtxVal g1 -> (NCtxVal g2, CtxVal g3)

instance σ ~ τ => CDivN ('End σ :: NCtx sig) ('End τ) ('Empty :: Ctx sig) where
--  splitN g = (g,())
instance CDivN ('Cons ('Just σ) g) ('End σ) ('N ('Cons 'Nothing g)) where
--  splitN (s,g) = (s,g)
instance (CMergeU u3 u2 u1, CDivN g1 g2 g3, g3' ~ ConsN u3 g3)
      => CDivN ('Cons u1 g1) ('Cons u2 g2) g3' where





