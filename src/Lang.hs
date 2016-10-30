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

  Unit :: LExp '[] One
  LetUnit :: Merge g1 g2 g3
          -> LExp g1 One
          -> LExp g2 t
          -> LExp g3 t

  Pair :: Merge g1 g2 g3
       -> LExp g1 s
       -> LExp g2 t
       -> LExp g3 (s ⊗ t)
  LetPair :: Merge g1 g2 g3
          -> AddCtx x s g2  g2'
          -> AddCtx y t g2' g2''
          -> LExp g1 (s ⊗ t)
          -> LExp g2'' r
          -> LExp g3 r 

  ETuple :: LExps g ts
         -> LExp g (Tuple ts)
  Case :: Merge g1 g2 g3
       -> AddPat p s g2 g2'
       -> LExp g1 s
       -> LExp g2' t
       -> LExp g3 t

  Put     :: EmptyCtx g -> a -> LExp g (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp g1 (Lower a)
      -> (a -> LExp g2 t)
      -> LExp g3 t

  Shift   :: Shift i g1 g2 -> LExp g1 t -> LExp g2 t
  Unshift :: Shift i g1 g2 -> LExp g2 t -> LExp g1 t

expToSCtx :: LExp g t -> SCtx g
expToSCtx = undefined


data LExps :: Ctx -> [LType] -> * where
  LExpNil  :: LExps '[] '[]
  LExpCons :: Merge g1 g2 g3 
           -> LExp  g1 t
           -> LExps g2 ts
           -> LExps g3 (t ': ts)

-- values

shift1 :: LExp g t -> LExp ('Unused ': g) t
shift1 = Shift ShiftHere

unshift1 :: LExp ('Unused ': g) t -> LExp g t
unshift1 = Unshift ShiftHere

data LVal :: LType -> * where
  VUnit :: LVal One
  VPair :: LVal s -> LVal t -> LVal (s ⊗ t)
  VTuple :: LVals ts -> LVal (Tuple ts)
  
  VAbs :: forall x s t g g'.
         EmptyCtx g 
      -> AddCtx x s g g'
      -> LExp g' t
      -> LVal (s ⊸ t)
  VPut :: a -> LVal (Lower a)

data LVals :: [LType] -> * where
  VNil :: LVals '[]
  VCons :: LVal s -> LVals ts -> LVals (s ': ts)

valToExp :: LVal t -> LExp '[] t
valToExp (VAbs pfE pfAdd e) = transportDown pfE $ Abs pfAdd e
valToExp (VPut a) = Put EmptyNil a
valToExp VUnit = Unit
valToExp (VPair s t) = Pair MergeE (valToExp s) (valToExp t)

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
  show Unit            = "()"
  show (LetUnit _ s t) = "let () = " ++ show s ++ " in " ++ show t
  show (Pair _ s t)    = "(" ++ show s ++ ", " ++ show t ++ ")"
  show (LetPair _ pfA1 pfA2 s t) = "let (" ++ x ++ "," ++ y ++ ") = " ++ show s ++ " in " ++ show t
    where
      x = show pfA1 
      y = show pfA2
  show (Abs pfAdd e)   = "λ" ++ show pfAdd ++ ". " ++ show e
  show (App _ e1 e2)   = show e1 ++ " " ++ show e2
  show (Case _ _ _ _)  = undefined
  show (Put _ a)       = show "PUT"
  show (LetBang _ e f) = show e ++ " >! " ++ show "FUN"
  show (Shift _ e)     = show e
  show (Unshift _ e)   = show e




-- Substitution ------------------------------------------------------
{-
subst :: forall x s t g g'.
         AddCtx x s g g'
      -> LExp '[] s 
      -> LExp g' t 
      -> LExp g  t
subst pfAdd s (Var pfSing2)        = substVar pfAdd s pfSing2
subst pfAdd s (Abs pfAdd' e')      = substAbs pfAdd s pfAdd' e'
subst pfAdd s (App pfMerge e1 e2)  = substApp pfAdd s pfMerge e1 e2
subst pfAdd s (Put pfEmpty a)      = substPut pfAdd s pfEmpty a
subst pfAdd s (LetBang pfM e f)    = substLetBang pfAdd s pfM e f
subst pfAdd s (Shift pfS e)        = substShift pfAdd s pfS e
-- pfAdd :: AddCtx x s g g'
-- s :: LExp '[] s
-- pfS :: Shift g0 g'
-- e :: LExp g' t
subst pfAdd s (Unshift pfS e)      = substUnshift pfAdd s pfS e
  

substVar :: AddCtx x s g g'
         -> LExp '[] s
         -> SingletonCtx y t g'
         -> LExp g t
substVar pfAdd s pfSing = 
  case addSingletonInv pfAdd pfSing of 
    Dict -> transportUp pfEmpty s
      where
        pfEmpty = addSingletonEmpty pfAdd pfSing

substAbs :: forall x y s t1 t2 g1 g2 g3.
            AddCtx x s g1 g2
         -> LExp '[] s
         -> AddCtx y t1 g2 g3
         -> LExp g3 t2
         -> LExp g1 (t1 ⊸ t2)
substAbs pfAddX s pfAddY e = Abs pfAddY' $ subst pfAddX' s e 
  where
    (pfAddY', pfAddX') = addTwice pfAddX pfAddY


substApp :: AddCtx x s g0 g
         -> LExp '[] s
         -> Merge g1 g2 g
         -> LExp g1 (t1 ⊸ t2)
         -> LExp g2 t1
         -> LExp g0 t2
substApp pfA s pfM e1 e2 = 
  case mergeAdd pfM pfA of
                       -- pfA' :: AddCtx x s (Remove x g1) g1
                       -- pfM' :: Merge (Remove x g1) g2 (Remove x g)
    Left  (pfA', pfM') -> App pfM' (subst pfA' s e1) e2
    Right (pfA', pfM') -> App pfM' e1 (subst pfA' s e2)


substLetBang :: AddCtx x s g g'
             -> LExp '[] s
             -> Merge g1 g2 g'
             -> LExp g1 (Lower a)
             -> (a -> LExp g2 t)
             -> LExp g t
substLetBang pfA s pfM e f =
  case mergeAdd pfM pfA of
    Left  (pfA', pfM') -> LetBang pfM' (subst pfA' s e) f
    Right (pfA', pfM') -> LetBang pfM' e (\ x -> subst pfA' s (f x))

substPut :: AddCtx x s g g'
         -> LExp '[] s
         -> EmptyCtx g'
         -> a
         -> LExp g (Lower a)
substPut pfA _ pfE _ = addEmptyAbsurd pfA pfE

substShift :: forall x s t g0 g g'. AddCtx x s g g'
           -> LExp '[] s
           -> Shift g0 g'
           -> LExp g0 t
           -> LExp g t
substShift pfAdd s pfShift e = Shift pfShift' $ subst pfAdd' s e
  where
    -- pfAdd'   :: AddCtx x s (Remove x g0) g0
    -- pfShift' :: Shift (Remove x g0) g
    (pfAdd',pfShift') = addShift pfAdd pfShift

substUnshift :: AddCtx x s g g'
             -> LExp '[] s
             -> Shift g' g''
             -> LExp g'' t
             -> LExp g   t
substUnshift pfA s pfS e = Unshift pfShift' $ subst pfAdd' s e
  where
    (pfAdd',pfShift') = addShift2 pfA pfS
-}

-- Evaluation --------------------------------------------


fromVPut :: LVal (Lower a) -> a
fromVPut (VPut a) = a

{-
eval' :: forall g s. EmptyCtx g -> LExp g s -> LVal s
-- Abstraction is a value
-- pfEmpty :: EmptyCtx g
-- pfAdd   :: AddCtx x s g g'
-- e       :: LExp g' t
eval' pfEmpty (Abs pfAdd e)           = absToLVal pfEmpty pfAdd e
-- VAbs pfSing e'
--  where
--    (pfSing, e') = transportDownSing pfEmpty pfAdd e

-- APPLICATION
-- pfEmpty :: EmptyCtx g
-- pfMerge :: Merge g1 g2 g
-- e1      :: LExp g1 (s ⊸ t)
-- e2      :: LExp g2 s
-- eval pfEmpty2 e2 :: LExp '[] s
-- eval' pfEmpty1 e1 :: LVal '[] (s ⊸ t)
eval' pfEmpty (App pfMerge e1 e2)     = 
  case (eval' pfEmpty1 e1, eval pfEmpty2 e2) of
    -- pfSing :: SingletonCtx x s g0
    -- e1'    :: LExp g0 t
    -- e2'    :: LExp '[] s
    (VAbs pfE pfA e1', e2') -> eval' EmptyNil e'
         where
           e' = transportDown pfE $ subst pfA e2' e1'

  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty

-- Put is a value
eval' pfEmpty (Put pf a)               = VPut a
-- LetBang
-- pfEmpty :: EmptyCtx g
-- pfMerge :: Merge g1 g2 g
-- e :: LExp g1 (Lower a)
-- k :: a -> LExp g2 t
eval' pfEmpty (LetBang pfMerge e k) = 
  eval' EmptyNil $ transportDown pfEmpty2 (k a)
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
    a                   = fromVPut $ eval' pfEmpty1 e

-- pfE :: EmptyCtx g2
-- pfS :: Shift g1 g2
-- e   :: LExp g1 t
-- (Shift pfS e) :: LExp g2 s
eval' pfE             (Shift pfS e)   = eval' (unshiftEmpty pfS pfE) e
-- pfE :: EmptyCtx g1
-- pfS :: Shift g1 g2
-- e   :: LExp g2 t
-- (Unshift pfS e) :: LExp g1 s
eval' pfE             (Unshift pfS e) = eval' (shiftEmpty pfS pfE) e


eval :: forall f g s. EmptyCtx g -> LExp g s -> LExp '[] s
eval pfEmpty e = valToExp $ eval' pfEmpty e
-}

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


