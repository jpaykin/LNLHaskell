{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, LambdaCase,
             EmptyCase, FlexibleContexts
#-}

module Eval where

import Data.Kind
import Data.Constraint

import Types
import Context
import Proofs
import Lang 
import Subst

-- Evaluation --------------------------------------------

eval :: forall sig (dom :: Dom sig) (s :: LType sig).
        Monad (SigEffect sig)
     => LExp dom 'Empty s 
     -> SigEffect sig (LExp dom 'Empty s)
eval e = fmap valToExp $ eval' e


eval' :: forall sig (dom :: Dom sig) (s :: LType sig).
         Monad (SigEffect sig)
      => LExp dom 'Empty s -> SigEffect sig (LVal dom s)
eval' (Dom pfIn e)         = evalDomain pfIn e
-- eval' (Abs pfA e)       = return $ VAbs pfA e
-- eval' (App pfM e1 e2) = 
--   case mergeEmpty pfM of {Dict -> do
--     VAbs pfA e1' <- eval' e1
--     e2'          <- eval e2
--     case addRemoveEquiv pfA of {Dict -> 
--     eval' $ subst pfA e2' e1'
--   }}
-- eval' Unit                          = return VUnit
-- eval' (LetUnit pfM e1 e2)           = 
--   case mergeEmpty pfM of {Dict -> do
--     VUnit <- eval' e1
--     eval' e2
--   }
-- eval' (Pair pfM e1 e2)              = 
--   case mergeEmpty pfM of {Dict -> do
--     v1 <- eval' e1
--     v2 <- eval' e2
--     return $ VPair v1 v2
--   }
-- eval' (LetPair pfM pfA1 pfA2 e1 e2) = evalLetPair pfM pfA1 pfA2 e1 e2
-- eval' (Prod e1 e2)                  = do
--   v1 <- eval' e1
--   v2 <- eval' e2
--   return $ VProd v1 v2
-- eval' (Fst e)                       = do
--   VProd v1 v2 <- eval' e
--   return v1
-- eval' (Snd e)                       = do
--   VProd v1 v2 <- eval' e
--   return v2
-- eval' (Inl e)                       = fmap VInl $ eval' e
-- eval' (Inr e)                       = fmap VInr $ eval' e
-- eval' (Case pfM pfA1 pfA2 e e1 e2)  = evalCase pfM pfA1 pfA2 e e1 e2
-- eval' (Put a)                       = return $ VPut a
-- eval' (LetBang pfM e f)             = 
--   case mergeEmpty pfM of {Dict -> do
--     VPut a <- eval' e
--     eval' $ f a
--   }
  

-- evalLetPair :: forall dom g1 g2 x1 x2 t1 t2 g2' g2'' r. 
--             Domain dom => Merge g1 g2 'Empty
--          -> AddCtx x1 t1 g2 g2'
--          -> AddCtx x2 t2 g2' g2''
--          -> LExp dom g1 (t1 ⊗ t2)
--          -> LExp dom g2'' r
--          -> DomEffect dom (LVal dom r)
-- evalLetPair pfM pfA1 pfA2 e1 e2 = 
--   case mergeEmpty pfM of {Dict -> 
--   case addRemoveEquiv pfA1 of {Dict ->
--   case addRemoveEquiv pfA2 of {Dict -> do
--     VPair v1 v2 <- eval' e1
--     eval' $ substVal pfI1'' v1 $ substVal pfI2 v2 e2
--   }}}
--   -- case eval' e1 of 
--   --   VPair v1 v2 -> 
--   --     case addRemoveEquiv pfA1 of {Dict ->
--   --     case addRemoveEquiv pfA2 of {Dict -> eval' e2''}}
--   --     where
--   --       e2' :: LExp (Remove x2 g2'') r
--   --       e2' = substVal pfI2 v2 e2
--   --       e2'' :: LExp (Remove x1 (Remove x2 g2'')) r
--   --       e2'' = substVal pfI1'' v1 e2'
--   -- }
--   where
--     pfD :: Disjoint x1 x2
--     pfD = disjointIn pfI1 pfA2
--     pfI1 :: In x1 t1 g2'
--     pfI1 = addIn pfA1
--     pfI1' :: In x1 t1 g2''
--     pfI1' = inAdd pfI1 pfA2
--     pfI1'' :: In x1 t1 (Remove x2 g2'')
--     pfI1'' = disjointRemove pfD pfI1' pfI2
--     pfI2 :: In x2 t2 g2''
--     pfI2 = addIn pfA2

-- evalCase :: forall dom g g1 g2 x1 s1 g21 x2 s2 g22 t.
--             Domain dom => Merge g1 g2 'Empty
--          -> AddCtx x1 s1 g2 g21
--          -> AddCtx x2 s2 g2 g22
--          -> LExp dom g1 (s1 ⊕ s2)
--          -> LExp dom g21 t
--          -> LExp dom g22 t
--          -> DomEffect dom (LVal dom t)
-- evalCase pfM pfA1 pfA2 e e1 e2 = 
--   case mergeEmpty pfM      of {Dict -> 
--   case addRemoveEquiv pfA1 of {Dict ->
--   case addRemoveEquiv pfA2 of {Dict -> do
--     v <- eval' e
--     case v of
--       VInl v1 -> eval' (substVal pfI1 v1 e1)
--       VInr v2 -> eval' (substVal pfI2 v2 e2)
--   }}}
--   where
--     pfI1 :: In x1 s1 g21
--     pfI1 = addIn pfA1
--     pfI2 = addIn pfA2
    
    


-- substVal :: Domain dom => In x s g 
--          -> LVal dom s -> LExp dom g t -> LExp dom (Remove x g) t
-- substVal pfI v e = subst' pfI (valToExp v) e


