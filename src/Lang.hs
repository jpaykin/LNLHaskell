{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase
#-}

module Lang where

import Data.Kind
import Data.Constraint

import Types
import Context


  
data LExp :: Ctx -> LType -> * where
--  Var :: LExp _ [(x,t)] t
  Var :: forall x t f1 f2 g. SingletonCtx x t g -> LExp g t
  
  Abs :: forall x s t g g'. 
         AddCtx x s g g' 
      -> LExp g' t
      -> LExp g (s ⊸ t)
  App :: Merge g1 g2 g3
      -> LExp g1 (s ⊸ t)
      -> LExp g2 s
      -> LExp g3 t

  Pair :: Merge g1 g2 g3
       -> LExp g1 t1
       -> LExp g2 t2
       -> LExp g3 (t1 ⊗ t2)
  LetPair :: Merge g1 g2 g3
       -> AddCtx x1 t1 g2 g2'
       -> AddCtx x2 t2 g2' g2''
       -> LExp g1 (t1 ⊗ t2)
       -> LExp g2'' r
       -> LExp g3   r

  Put     :: EmptyCtx g -> a -> LExp g (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp g1 (Lower a)
      -> (a -> LExp g2 t)
      -> LExp g3 t

  Shift   :: Shift i g1 g2 -> LExp g1 t -> LExp g2 t
  Unshift :: Shift i g1 g2 -> LExp g2 t -> LExp g1 t

-- values

shift1 :: LExp g t -> LExp ('Unused ': g) t
shift1 = Shift ShiftHere

unshift1 :: LExp ('Unused ': g) t -> LExp g t
unshift1 = Unshift ShiftHere

data LVal :: LType -> * where
  VAbs :: forall x s t g g'.
         EmptyCtx g 
      -> AddCtx x s g g'
      -> LExp g' t
      -> LVal (s ⊸ t)
  VPut :: a -> LVal (Lower a)
  VPair :: LVal t1 -> LVal t2 -> LVal (t1 ⊗ t2)

valToExp :: LVal t -> LExp '[] t
valToExp (VAbs pfE pfAdd e) = transportDown pfE $ Abs pfAdd e
valToExp (VPut a) = Put EmptyNil a
valToExp (VPair v1 v2) = Pair MergeE (valToExp v1) (valToExp v2)

instance Num Nat where
  Z   + n   = n
  S m + n   = S (m+n)
  Z   - n   = Z
  m   - Z   = m
  S m - S n = m - n
  Z   * n   = Z
  S m * n   = m * n + n
  abs e     = e
  signum e  = S Z
  fromInteger = undefined
  negate e    = undefined


singToNat :: SingletonCtx x s g -> Nat
singToNat AddHereS = Z
singToNat (AddLaterS pf) = S $ singToNat pf

addToNat :: AddCtx x s g g' -> Nat
addToNat AddEHere = Z
addToNat (AddHere _) = Z
addToNat (AddELater pf) = S (addToNat pf)
addToNat (AddLater pf) = S (addToNat pf)

toInt :: Nat -> Int
toInt Z = 0
toInt (S n) = toInt n + 1

instance Show Nat where
  show n = show $ toInt n

-- show the variable 
instance Show (SingletonCtx x s g) where
  show pf = show $ singToNat pf

-- show the variable
instance Show (AddCtx x s g g') where
  show pf = show $ addToNat pf

instance Show (LExp g t) where
  show (Var pfSing)    = show pfSing
  show (Abs pfAdd e)   = "λ" ++ show pfAdd ++ ". " ++ show e
  show (App _ e1 e2)   = show e1 ++ " " ++ show e2
  show (Put _ a)       = show "PUT"
  show (LetBang _ e f) = show e ++ " >! " ++ show "FUN"
  show (Shift _ e)     = show e
  show (Unshift _ e)   = show e


-- transport --------------------------------------------

transport :: EquivEmpty g1 g2 -> LExp g1 t -> LExp g2 t
transport EquivENil e = e
transport (EquivEEL pfEmpty) e = transportUp pfEmpty e
transport (EquivEER pfEmpty) e = transportDown pfEmpty e
transport (EquivECons pfEquiv) e = 
    shift1 $ transport pfEquiv $ unshift1 e

transportDown :: EmptyCtx g -> LExp g t -> LExp '[] t
transportDown EmptyNil       e = e
transportDown (EmptyCons pf) e = transportDown pf $ unshift1 e

    
transportUp :: EmptyCtx g -> LExp '[] t -> LExp g t
transportUp EmptyNil       e = e
transportUp (EmptyCons pf) e = shift1 $ transportUp pf e


