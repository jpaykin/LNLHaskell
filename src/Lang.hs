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

-- values

data LVal :: Ctx -> LType -> * where
  VAbs :: forall x s t g g'. 
         EmptyCtx g
      -> AddCtx x s g g' 
      -> LExp g' t
      -> LVal g (s ⊸ t)
  VPut :: EmptyCtx g -> a -> LVal g (Lower a)

valToExp :: LVal g t -> LExp g t
valToExp (VAbs _ pfAdd e) = Abs pfAdd e
valToExp (VPut pf a) = Put pf a

-- Substitution ------------------------------------------------------

subst :: forall x s t g0 g1 g2 g3.
         EmptyCtx g1
      -> AddCtx x s g0 g2 
      -> LExp g1 s 
      -> LExp g2 t 
      -> LExp g0 t
subst pfEmpty1 pfAdd s (Var pfSing) = 
  case addSingletonInv pfAdd pfSing of {Dict -> 
  let pfEmpty2 = addSingletonEmpty pfAdd pfSing
  in transport s pfEmpty1 pfEmpty2
  } 
subst pfEmpty pfAdd s (Abs pfAdd2 e')      = substAbs pfEmpty s pfAdd pfAdd2 e'
subst pfEmpty pfAdd s (App pfMerge e1 e2)  = substApp pfEmpty s pfAdd pfMerge e1 e2
subst _       pfAdd s (Put _ a)            = case pfAdd of 
subst _       pfAdd s (LetBang _ _ _)      = case pfAdd of
  

substAbs :: EmptyCtx g
         -> LExp g s
         -> AddCtx x s  g0  g1
         -> AddCtx y t1 g1 g2
         -> LExp g2 t2
         -> LExp g0 (t1 ⊸ t2)
substAbs pfEmpty s pfAddX pfAddY e = Abs pfAddY' $ subst pfEmpty pfAddX' s e
  -- since (x:s)∈g1  and g1[x |-> s]=g2,
  -- we also have (x:s)∈g2
  -- and so ∃ g1' such that AddCtx x s f1 f2 g1' g2
  -- and AddCtxy t f1' f2' g0 g1'
  -- with this we can get a substitution g1' |- e{s/x} and
  -- g0 |- λ x.e{s/x}
  where
    (pfAddY', pfAddX') = addTwice pfAddX pfAddY

substApp :: EmptyCtx g
         -> LExp g s
         -> AddCtx x s g0 g3 
         -> Merge g1 g2 g3
         -> LExp g1 (t1 ⊸ t2)
         -> LExp g2 t1
         -> LExp g0 t2
substApp pfEmpty s pfAdd pfMerge e1 e2 = 
  case mergeAdd pfMerge pfAdd of
    Left  (pfAdd1, pfMerge1) -> App pfMerge1 (subst pfEmpty pfAdd1 s e1) e2
    Right (pfAdd2, pfMerge2) -> App pfMerge2 e1 (subst pfEmpty pfAdd2 s e2)
  -- since (x:s)∈g3 and Merge g1 g2 g3, 
  -- (x:s) ∈ g1 or (x:s) ∈ g2.


fromVPut :: forall g a. LVal g (Lower a) -> a
fromVPut (VPut _ a) = a

eval' :: forall g s. EmptyCtx g -> LExp g s -> LVal g s
-- Abstraction is a value
eval' pfEmpty (Abs pfAdd e)           = VAbs pfEmpty pfAdd e
-- Application
eval' pfEmpty (App pfMerge e1 e2)     = 
  case (eval' pfEmpty1 e1, eval pfEmpty2 e2) of
    (VAbs _ pfAdd e1', e2') -> 
--       case emptyUnique pfEmpty1 pfEmpty of
--         Dict -> 
         eval' pfEmpty $ transport (subst pfEmpty2 pfAdd e2' e1') pfEmpty1 pfEmpty
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
-- Put is a value
eval' pfEmpty (Put pf a)               = VPut pf a
-- LetBang
eval' pfEmpty (LetBang pfMerge e k) = eval' pfEmpty $ transport (k a) pfEmpty2 pfEmpty
  -- case emptyUnique pfEmpty2 pfEmpty of Dict -> eval' pfEmpty2 $ k a
  where
    (pfEmpty1,pfEmpty2) = mergeEmpty pfMerge pfEmpty
    v                   = eval' pfEmpty1 e
    a                   = fromVPut v


eval :: forall f g s. EmptyCtx g -> LExp g s -> LExp g s
eval pfEmpty e = valToExp $ eval' pfEmpty e


-- transport --------------------------------------------

transport :: LExp g1 t -> EmptyCtx g1 -> EmptyCtx g2 -> LExp g2 t
transport e pf1 pf2 = transportUp pf2 $ transportDown pf1 e


-- transportEquiv :: Equiv g1 g2 -> LExp g1 t -> LExp g2 t
-- transportEquiv EquivNil            e = e
-- transportEquiv (EquivEL pfEmpty)   e = transportUp pfEmpty e
-- transportEquiv (EquivER pfEmpty)   e = transportDown pfEmpty e
-- transportEquiv (EquivCons pfEquiv) e = undefined -- transportMap pfEquiv e
-- --    transportCons $ transportEquiv pfEquiv $ transportUncons e


-- transportMap :: Append g g1 g1' -> Append g g2 g2' 
--              -> Equiv g1 g2 -> LExp g1' t -> LExp g2' t
-- -- g=g1=g2='[], so g1'=g2'='[]
-- transportMap AppendNil AppendNil eq e = transportEquiv eq e
-- transportMap (AppendCons pf1) (AppendCons pf2) EquivNil e = undefined
-- transportMap _ _ (EquivEL pfEmpty) e = undefined
-- transportMap _ _ (EquivER pfEmpty) e = undefined
-- transportMap (AppendCons pf1) (AppendCons pf2) (EquivCons pfEquiv) e = undefined
-- --  undefined -- transportMap pfEmpty e


transportDown :: EmptyCtx g -> LExp g t -> LExp '[] t
transportDown pfE (Abs pfAdd e) = transportDownSing (addEmpty pfE pfAdd) e

transportDownSing :: SingletonCtx x s g -> LExp g t -> LExp '[] (s ⊸ t)
transportDownSing = undefined

-- transportDown EmptyNil e = e
-- transportDown (EmptyCons pf) e = transportDown pf $ transportUncons e

-- NOT BY SHIFTING THE TERM
-- use proofs instead
transportUncons :: LExp ('Unused ': g) t -> LExp g t
transportUncons (Var (AddLaterS pfSing)) = Var pfSing
transportUncons (Abs pfAdd e)            = undefined
transportUncons (App pfMerge e1 e2)      = undefined
transportUncons (Put (EmptyCons pfEmpty) a)          = Put pfEmpty a
transportUncons (LetBang pfMerge e f)    = undefined 



transportUp :: EmptyCtx g -> LExp '[] t -> LExp g t
transportUp EmptyNil e = e
transportUp (EmptyCons pf) e = transportCons $ transportUp pf e

-- MAYBE ALSO NOT BY SHIFTING?
transportCons :: LExp g t -> LExp ('Unused ': g) t
transportCons (Var pfSing) = Var (AddLaterS pfSing)
transportCons (Abs pfAdd e) = Abs (AddLater pfAdd) $ transportCons e
transportCons (App pfMerge e1 e2) = App (MergeU pfMerge) (transportCons e1) (transportCons e2)
transportCons (Put pfEmpty a) = Put (EmptyCons pfEmpty) a
transportCons (LetBang pfMerge e f) = LetBang (MergeU pfMerge) (transportCons e) f'
  where
    f' a = transportCons (f a)

