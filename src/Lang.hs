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

  Put     :: EmptyCtx g -> a -> LExp g (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp g1 (Lower a)
      -> (a -> LExp g2 t)
      -> LExp g3 t

  Shift   :: Shift g1 g2 -> LExp g1 t -> LExp g2 t
  Unshift :: Shift g1 g2 -> LExp g2 t -> LExp g1 t

-- values

shift1 :: LExp g t -> LExp ('Unused ': g) t
shift1 = Shift ShiftHere

unshift1 :: LExp ('Unused ': g) t -> LExp g t
unshift1 = Unshift ShiftHere

data LVal :: LType -> * where
  VAbs :: forall x s t g.
         SingletonCtx x s g
      -> LExp g t
      -> LVal (s ⊸ t)
  VPut :: a -> LVal (Lower a)

valToExp :: LVal t -> LExp '[] t
valToExp (VAbs pfSing e) = Abs (singletonAdd pfSing) e
valToExp (VPut a) = Put EmptyNil a

instance Num Nat where
  _ + _ = undefined
  _ - _ = undefined
  _ * _ = undefined
  abs e = e
  signum e = undefined
  fromInteger = undefined
  negate e = undefined


singToNat :: SingletonCtx x s g -> Nat
singToNat AddHereS = Z
singToNat (AddLaterS pf) = S $ singToNat pf

addToNat :: AddCtx x s g g' -> Nat
addToNat AddEHere = Z
addToNat AddHere = Z
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

-- Substitution ------------------------------------------------------

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
substApp = undefined
-- substApp :: EmptyCtx g
--          -> LExp g s
--          -> AddCtx x s g0 g3 
--          -> Merge g1 g2 g3
--          -> LExp g1 (t1 ⊸ t2)
--          -> LExp g2 t1
--          -> LExp g0 t2
-- substApp pfEmpty s pfAdd pfMerge e1 e2 = 
--   case mergeAdd pfMerge pfAdd of
--     Left  (pfAdd1, pfMerge1) -> App pfMerge1 (subst pfEmpty pfAdd1 s e1) e2
--     Right (pfAdd2, pfMerge2) -> App pfMerge2 e1 (subst pfEmpty pfAdd2 s e2)
--   -- since (x:s)∈g3 and Merge g1 g2 g3, 
--   -- (x:s) ∈ g1 or (x:s) ∈ g2.


substLetBang :: AddCtx x s g g'
             -> LExp '[] s
             -> Merge g1 g2 g'
             -> LExp g1 (Lower a)
             -> (a -> LExp g2 t)
             -> LExp g t
substLetBang = undefined

substPut :: AddCtx x s g g'
         -> LExp '[] s
         -> EmptyCtx g'
         -> a
         -> LExp g (Lower a)
substPut pfA _ pfE _ = addEmptyAbsurd pfA pfE

substShift :: AddCtx x s g g'
           -> LExp '[] s
           -> Shift g0 g'
           -> LExp g0 t
           -> LExp g t
substShift (AddELater pfA) s ShiftHere            e = subst pfA s e
substShift (AddELater pfA) s (ShiftLater pfShift) e = undefined
substShift (AddLater pfA)  s ShiftHere            e = undefined
substShift (AddLater pfA)  s (ShiftLater pfShift) e = undefined
  -- Shift $ subst pfA s e

substUnshift :: AddCtx x s g g'
             -> LExp '[] s
             -> Shift g' g''
             -> LExp g'' t
             -> LExp g   t
substUnshift pfA s pfS e = undefined -- Unshift pfS e'
 where
--  e' :: LExp (ShiftF pfS g) t
    e' = subst undefined s e
--  pfA' :: AddCtx x s (ShiftF pfS g) g''

-- Unshift pfS $ subst (AddLater pfA) s e


-- Evaluation --------------------------------------------


fromVPut :: forall g a. LVal (Lower a) -> a
fromVPut (VPut a) = a

absToLVal :: EmptyCtx g -> AddCtx x s g g' -> LExp g' t -> LVal (s ⊸ t)
absToLVal _ _ _ = undefined

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
    (VAbs pfSing e1', e2') -> eval' EmptyNil e'
         where
           e' = subst (singletonAdd pfSing) e2' e1'

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

eval' (EmptyCons pfE) (Shift _ e)   = undefined -- eval' pfE e
eval' pfE             (Unshift _ e) = undefined -- eval' (EmptyCons pfE) e


eval :: forall f g s. EmptyCtx g -> LExp g s -> LExp '[] s
eval pfEmpty e = valToExp $ eval' pfEmpty e


-- transport --------------------------------------------

-- transport :: LExp g1 t -> EmptyCtx g1 -> EmptyCtx g2 -> LExp g2 t
-- transport e pf1 pf2 = transportUp pf2 $ transportDown pf1 e

transport :: EquivEmpty g1 g2 -> LExp g1 t -> LExp g2 t
transport EquivENil e = e
transport (EquivEEL pfEmpty) e = transportUp pfEmpty e
transport (EquivEER pfEmpty) e = transportDown pfEmpty e
transport (EquivECons pfEquiv) e = 
    shift1 $ transport pfEquiv $ unshift1 e



transportDown :: EmptyCtx g -> LExp g t -> LExp '[] t
transportDown EmptyNil       e = e
transportDown (EmptyCons pf) e = transportDown pf $ unshift1 e


-- transportSnoc :: Snoc g 'Unused g' -> LExp g' t -> LExp g t
-- transportSnoc SnocNil        e = transportDown (EmptyCons EmptyNil) e
-- -- g ~ u' ': g0
-- -- g' ~ u' ': g0'
-- -- pfS :: Snoc g0 Unused g0'
-- -- e :: LExp (u' ': g0')
-- transportSnoc (SnocCons pfS) e = undefined -- ???

-- transportDownSingHere :: EmptyCtx g
--                       -> LExp ('Used s ': g) t
--                       -> LExp '[ 'Used s ] t
-- transportDownSingHere EmptyNil       e = e
-- transportDownSingHere (EmptyCons pf) e = 
--   transportDownSingHere pf $ transportSnoc (SnocCons (SnocCons SnocNil)) e

-- transportDownSing' :: SingletonCtx x s g' 
--                    -> LExp g' t
--                    -> (SingletonCtx x s (Sing x s), LExp (Sing x s) t)
-- transportDownSing' = undefined

-- transportDownSing :: EmptyCtx g 
--                   -> AddCtx x s g g' 
--                   -> LExp g' t 
--                   -> (SingletonCtx x s (Sing x s), LExp (Sing x s) t)
-- transportDownSing EmptyNil         pfAdd          e = 
--   transportDownSing' (addSingleton pfAdd) e
-- transportDownSing (EmptyCons pfE) pfAdd           e = help pfE pfAdd

-- help :: EmptyCtx g
--      -> AddCtx x s ('Unused ': g) g'
--      -> LExp g' t
--      -> (SingletonCtx x s (Sing x s), LExp (Sing x s) t)
-- -- g is empty
-- -- g' is empty
-- help pfE AddHere e = (AddHereS, e)



-- g ~ 'Unused ': g0
-- pfE :: EmptyCtx g0
-- g' ~ 'Used s ': g0
-- e :: LExp ('Used s ': g0) t
-- x ~ 'Z
-- want: (SingletonCtx Z s [Used s], LExp [Used s] t)
-- transportDownSing (EmptyCons pfE)  AddHere        e = undefined
-- g ~ 'Unused ': g0
-- pfE :: EmptyCtx g0
-- x ~ 'S x'
-- g' ~ 'Unused ': g0'
-- pfA :: AddCtx x' s g0 g0'
-- e   :: LExp ('Unused ': g0') t
-- want: ( SingletonCtx (S x') s ('Unused ': Sing x' s)
--       , LExp ('Unused ': Sing x' s) t )
-- transportDownSing (EmptyCons pfE) (AddLater pfA)  e = 
--   (AddLaterS pfS, Shift e')
--   where
--     (pfS, e') = transportDownSing pfE pfA (Unshift e)
    
transportUp :: EmptyCtx g -> LExp '[] t -> LExp g t
transportUp EmptyNil       e = e
transportUp (EmptyCons pf) e = shift1 $ transportUp pf e



-- transportDown EmptyNil e = e
-- transportDown (EmptyCons pf) e = transportDown pf $ transportUncons e

-- NOT BY SHIFTING THE TERM
-- use proofs instead
-- transportUncons :: LExp ('Unused ': g) t -> LExp g t
-- transportUncons (Var (AddLaterS pfSing)) = Var pfSing
-- transportUncons (Abs pfAdd e)            = undefined
-- transportUncons (App pfMerge e1 e2)      = undefined
-- transportUncons (Put (EmptyCons pfEmpty) a)          = Put pfEmpty a
-- transportUncons (LetBang pfMerge e f)    = undefined 



-- transportUp :: EmptyCtx g -> LExp '[] t -> LExp g t
-- transportUp EmptyNil e = e
-- transportUp (EmptyCons pf) e = transportCons $ transportUp pf e

-- MAYBE ALSO NOT BY SHIFTING?
-- transportCons :: LExp g t -> LExp ('Unused ': g) t
-- transportCons (Var pfSing) = Var (AddLaterS pfSing)
-- transportCons (Abs pfAdd e) = Abs (AddLater pfAdd) $ transportCons e
-- transportCons (App pfMerge e1 e2) = App (MergeU pfMerge) (transportCons e1) (transportCons e2)
-- transportCons (Put pfEmpty a) = Put (EmptyCons pfEmpty) a
-- transportCons (LetBang pfMerge e f) = LetBang (MergeU pfMerge) (transportCons e) f'
--   where
--     f' a = transportCons (f a)

