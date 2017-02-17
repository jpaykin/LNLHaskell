{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase, FlexibleContexts
#-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors 
                               -fno-warn-redundant-constraints #-}

module Classes where

import Prelude hiding (div)

import Prelim
--import Context
import Types
--import Proofs

-- Singleton instance

{-
class KnownUsage u where
  usg :: SUsage Phantom u

instance KnownUsage 'Nothing where
  usg = SNothing
instance KnownUsage ('Used σ) where
  usg = SUsed @_ @_ @σ Phantom

class KnownCtx g where
  ctx :: SCtx Phantom g
class KnownNCtx g where
  nctx :: SNCtx Phantom g

instance KnownCtx 'Empty where
  ctx = SEmpty
instance KnownNCtx g => KnownCtx ('N g) where
  ctx = SN nctx

instance KnownNCtx ('End τ) where
  nctx = SEnd Phantom
instance (KnownUsage u, KnownNCtx g) => KnownNCtx ('Cons u g) where
  nctx = SCons usg nctx
-}

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
    add :: LVal σ -> CtxVal γ -> CtxVal γ'
    remove :: CtxVal γ' -> (LVal σ, CtxVal γ)

instance CAddCtxN x σ g g' (IsSingleton g') => CAddCtx x σ g ('N g') where
  add = addN @_ @x @σ @g @g'
  remove = removeN @_ @x @σ @g @g'

-- If CAddCtxN x σ g g' flag then 
-- flag IFF g' is a singleton context IFF g is the empty context
class CAddCtxN (x :: Nat) (σ :: LType sig) (γ :: Ctx sig) (γ' :: NCtx sig) (flag :: Bool) 
      | x σ γ -> γ' flag, x γ' flag -> σ γ where
  addN :: LVal σ -> CtxVal γ -> NCtxVal γ'
  removeN :: NCtxVal γ' -> (LVal σ, CtxVal γ)

instance CSingletonNCtx x σ g' => CAddCtxN x σ Empty g' 'True where
  addN a _ = singleton @_ @x @σ a
  removeN g' = (singletonNInv @_ @x @σ g', ())
instance CAddNCtxN x σ g g' => CAddCtxN x σ ('N g) g' 'False where
  addN = addNN @_ @x @σ @g 
  removeN = removeNN @_ @x @σ @g @g'

class CAddNCtxN (x :: Nat) (σ :: LType sig) (γ :: NCtx sig) (γ' :: NCtx sig) | x σ γ -> γ', x γ' -> σ γ where
  addNN :: LVal σ -> NCtxVal γ -> NCtxVal γ'
  removeNN :: NCtxVal γ' -> (LVal σ, NCtxVal γ)

instance CAddNCtxFlag x σ g g' (IsDouble g') => CAddNCtxN x σ g g' where
  addNN = addNN' @_ @x @σ @g
  removeNN = removeNN' @_ @x @σ @g

-- If CAddNCtxFlag x σ g g' flag then
-- flag IFF g is a singleton context iff g' is a double context
class CAddNCtxFlag (x :: Nat) (σ :: LType sig) (γ :: NCtx sig) (γ' :: NCtx sig) (flag :: Bool) | x σ γ -> γ' flag, x γ' flag -> σ γ where
  addNN' :: LVal σ -> NCtxVal γ -> NCtxVal γ'
  removeNN' :: NCtxVal γ' -> (LVal σ, NCtxVal γ)

instance (IsSingleton g ~ flag)
    => CAddNCtxFlag 'Z σ ('Cons 'Nothing g) ('Cons ('Just σ) g) flag where
  addNN' s g = (s,g)
  removeNN' = id
instance CSingletonNCtx x σ g => CAddNCtxFlag ('S x) σ ('End τ) ('Cons ('Just τ) g) 'True where
  addNN' s t = (t,singleton @_ @x @σ s)
  removeNN' (v,g) = (singletonNInv @_ @x @σ g, v)
instance CAddNCtxFlag x σ g g' f => CAddNCtxFlag ('S x) σ ('Cons 'Nothing g) ('Cons 'Nothing g') f where
  addNN' s g = addNN' @_ @x @σ @g @g' s g
  removeNN' = removeNN'  @_ @x @σ @g
instance CAddNCtxN x σ g g' => CAddNCtxFlag ('S x) σ ('Cons ('Just τ) g) ('Cons ('Just τ) g') 'False where
  addNN' s (t,g) = (t,addNN @_ @x @σ @g @g' s g)
  removeNN' (v,g') = let (a,g0) = removeNN @_ @x @σ @g g'
                     in (a,(v,g0))


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
--  isSingleton :: Dict (IsSingleton g ~ flag)

instance CIsSingleton ('End σ) 'True where
--  isSingleton = Dict
instance CIsSingleton ('Cons ('Just σ) g) 'False where
--  isSingleton = Dict
instance CIsSingleton g b => CIsSingleton ('Cons 'Nothing g) b where
--  isSingleton = case isSingleton @g of Dict -> Dict

-- Singleton Context ------------------------------------------

class CSingletonCtx (x :: Nat) (σ :: LType sig) (g :: Ctx sig) | x σ -> g, g -> x σ where
  singleton :: LVal σ -> CtxVal g
  singletonInv :: CtxVal g -> LVal σ
class CSingletonNCtx (x :: Nat) (σ :: LType sig) (g :: NCtx sig) | x σ -> g, g -> x σ where
  singletonN :: LVal σ -> NCtxVal g
  singletonNInv :: NCtxVal g -> LVal σ

instance CSingletonNCtx 'Z σ ('End σ) where
  singletonN = id
  singletonNInv = id
instance CSingletonNCtx x σ g => CSingletonNCtx ('S x) σ ('Cons 'Nothing g) where
  singletonN = singletonN @_ @x @σ @g 
  singletonNInv = singletonNInv @_ @x @σ @g

instance CSingletonNCtx x σ g => CSingletonCtx x σ ('N g) where
  singleton = singletonN @_ @x @σ
  singletonInv = singletonNInv @_ @x @σ

-- Well-formed contexts --------------------------------

class (CDiv γ 'Empty γ, CDiv  γ γ 'Empty, CMergeForward 'Empty γ γ, CMergeForward γ 'Empty γ) => WFCtx γ 
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
    => CMerge g1 g2 g3 | g1 g2 -> g3, g1 g3 -> g2, g2 g3 -> g1 where
--  split :: CtxVal g3 -> (CtxVal g1, CtxVal g2)

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





