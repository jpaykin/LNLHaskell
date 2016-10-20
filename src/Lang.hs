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
import Frame


  
data LExp :: Ctx -> LType -> * where
  Var :: forall x t f1 f2 g. SingletonCtx x t f1 f2 g -> LExp g t
  Abs :: forall x s f1 f2 t g g'. 
         AddCtx x s f1 f2 g g' 
      -> LExp g' t
      -> LExp g (s ⊸ t)
  App :: Merge g1 g2 g3
      -> LExp g1 (s ⊸ t)
      -> LExp g2 s
      -> LExp g3 t

  Put     :: forall (f::Frame) (g::Ctx) a. EmptyCtx f g -> a -> LExp g (Lower a)
  LetBang :: Merge g1 g2 g3
      -> LExp g1 (Lower a)
      -> (a -> LExp g2 t)
      -> LExp g3 t

--  Force   :: CEmptyCtx g => Lift t -> LExp g t

data LVal :: Ctx -> LType -> * where
  VAbs :: forall x s f f1 f2 t g g'. 
         EmptyCtx f g
      -> AddCtx x s f1 f2 g g' 
      -> LExp g' t
      -> LVal g (s ⊸ t)
  VPut :: EmptyCtx f g -> a -> LVal g (Lower a)

valToExp :: LVal g t -> LExp g t
valToExp (VAbs _ pfAdd e) = Abs pfAdd e
valToExp (VPut pfEmpty a) = Put pfEmpty a


subst :: forall x s f f1 f2 t g0 g1 g2 g3. 
         EmptyCtx f g1
      -> AddCtx x s f1 f2 g0 g2 
      -> LExp g1 s -> LExp g2 t -> LExp g0 t
subst = undefined

-- pfEmpty :: EmptyCtx g1
-- pfAdd :: AddCtx x s g0 g2
-- s :: LExp g1 s
-- pfSing :: Singleton x' s' g2
-- subst pfEmpty1 pfAdd s (Var pfSing) =
--     case addSingletonCtxEq pfAdd pfSing of {(Dict,Dict) ->
--       transport pfEmpty1 pfEmpty2 s
--     }
--   where
--     pfEmpty2 = emptySing pfSing pfAdd
-- subst pfEmpty pfAdd s (Abs pfAdd2 e') = undefined
-- subst pfEmpty pfAdd s (App pfMerge2 e1 e2) = substApp pfEmpty s pfAdd pfMerge2 e1 e2 
-- subst pfEmpty pfAdd s (Put a) = case pfAdd of 
--     -- pfAdd :: AddCtx x s g0 g2
--     -- from Put we know g2 = []
-- subst pfEmpty pfAdd s (LetBang pfMerge2 e f) = case pfAdd of
  

-- substApp :: EmptyCtx g -> LExp g s
--          -> AddCtx x s g0 g3 -> Merge g1 g2 g3 -> LExp g1 (t1 ⊸ t2) -> LExp g2 t1
--          -> LExp g0 t2
-- substApp pfEmpty s pfAdd pfMerge e1 e2 = 
--   case containsMerge (addContains pfAdd) pfMerge of
--     Left  pfContains1 -> undefined
--     Right pfContains2 -> undefined

-- mergeEmptyEq1 (EmptyCons pfNil) MergeEmptyR = mergeEmptyEq1 pfNil MergeEmptyR
-- mergeEmptyEq1 (EmptyCons pfNil) (MergeR pfMerge) = 
--     case mergeEmptyEq1 pfNil pfMerge of Dict -> Dict
-- mergeEmptyEq1 (EmptyCons pfNil) (MergeU pfMerge) =
--     case mergeEmptyEq1 pfNil pfMerge of Dict -> Dict


-- (^) :: forall s t g1 g2 g3. (CEmptyCtx g1, CEmptyCtx g2, CEmptyCtx g3)
--     => LExp g1 (s ⊸ t) -> LExp g2 s
--     -> LExp g3 t
-- (Abs t) ^ s = undefined -- subst @_ @s @t @_ s t 


fromVPut :: forall a g. LVal g (Lower a) -> a
fromVPut (VPut _ a) = a

eval' :: forall f g s. EmptyCtx f g -> LExp g s -> LVal g s
eval' = undefined
-- eval' pfEmpty (App pfMerge e1 e2) = 
--   case v1 of
--     VAbs _ pfAdd e' -> 
--       eval' pfEmpty $ transport pfEmpty1 pfEmpty $ subst pfEmpty2 pfAdd e2' e'
--   where
--     v1                  = eval' pfEmpty1 e1
--     e2'                 = eval pfEmpty2 e2 -- call by value
-- --  e2'                 = e2               -- call by name
--     (pfEmpty1,pfEmpty2) = emptyMerge pfEmpty pfMerge
-- eval' pfEmpty (LetBang pfMerge e f) = 
--     eval' pfEmpty $ transport pfEmpty2 pfEmpty e2
--   where
--     v1                  = eval' pfEmpty1 e
--     e2                  = f $ fromVPut v1
--     (pfEmpty1,pfEmpty2) = emptyMerge pfEmpty pfMerge
-- eval' pfE (Abs pfA e) = VAbs pfE pfA e
-- eval' _ (Put a) = VPut a

eval :: forall f g s. EmptyCtx f g -> LExp g s -> LExp g s
eval pfEmpty e = valToExp $ eval' pfEmpty e

