{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, ScopedTypeVariables,
             EmptyCase
#-}

module Context where

import Data.Kind
import Data.Constraint

import Types


-- Equivalent Contexts ------------------------------------------

data Equiv  :: Ctx -> Ctx -> * where
  EquivNil  :: Equiv '[] '[]
  EquivEL   :: EmptyCtx g -> Equiv '[] g
  EquivER   :: EmptyCtx g -> Equiv g '[]
  EquivCons :: Equiv g1 g2 -> Equiv (u ': g1) (u ': g2)

-- Append -------------------------------------------------------

data Append  :: Ctx -> Ctx -> Ctx -> * where
  AppendNil  :: Append '[] g   g
  AppendCons :: Append g1 g2 g3 -> Append (u ': g1) g2 (u ': g3)

data AppendSnoc :: Ctx -> Ctx -> Ctx -> * where
  AppendNilR :: AppendSnoc g '[] g
  AppendSnoc :: Snoc g1 u g1' -> Append g1' g2 g3 -> AppendSnoc g1 (u ': g2) g3

data Snoc :: Ctx -> Usage -> Ctx -> * where
  SnocNil  :: Snoc '[] u '[u]
  SnocCons :: Snoc g u g' -> Snoc (u' ': g) u (u' ': g')

-- Empty Context ------------------------------------------------

data EmptyCtx :: Ctx -> * where
  EmptyNil  :: EmptyCtx '[]
  EmptyCons :: forall x g. EmptyCtx g -> EmptyCtx ('Unused ': g)



-- Add To Context ----------------------------------------------

-- AddCtx x t f1 f2 g g' 
-- f1++[(x,t)]++f2 is a frame for g and g'
data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddEHere   :: AddCtx 'Z s '[]            '[ 'Used s ]
  AddHere    :: AddCtx 'Z s ('Unused ': g) ('Used s ': g)
  AddELater  :: AddCtx x s '[] g -> AddCtx ('S x) s '[] ('Unused ': g)
  AddLater   :: AddCtx x s g g'  -> AddCtx ('S x) s (u ': g) (u ': g')


type family Insert x s g :: Ctx where
  Insert 'Z     s ('Unused ': g) = 'Used s ': g
  Insert ('S x) s (u       ': g) = u ': Insert x s g

--addCtxEquiv :: Equiv g1 g2 -> AddCtx x s g1 g' -> AddCtx x s g2 g'


-- Singleton Context ------------------------------------------

-- SingletonCtx x s f1 f2 g
-- f1++[(x,s)]++f2 is a frame for g
data SingletonCtx :: Nat -> LType -> Ctx -> * where
  AddHereS  :: SingletonCtx 'Z s '[ 'Used s ]
  AddLaterS :: SingletonCtx x s g
            -> SingletonCtx ('S x) s ('Unused ': g)

addEmpty :: EmptyCtx g -> AddCtx x s g g' -> SingletonCtx x s g'
addEmpty = undefined

addSingletonEmpty :: forall x s g g'. 
                     AddCtx x s g g' 
                  -> SingletonCtx x s g'
                  -> EmptyCtx g
addSingletonEmpty AddHere           AddHereS          = EmptyCons EmptyNil
addSingletonEmpty (AddLater pfAdd) (AddLaterS pfSing) = 
                  EmptyCons $ addSingletonEmpty pfAdd pfSing


addSingletonInv :: AddCtx x s g g' 
               -> SingletonCtx y t g' 
               -> Dict ('(x,s) ~ '(y,t))
addSingletonInv AddHere           AddHereS          = Dict
addSingletonInv (AddLater pfAdd) (AddLaterS pfSing) =
  case addSingletonInv pfAdd pfSing of Dict -> Dict

addInsert :: AddCtx x s g1 g2
          -> Dict (g2 ~ Insert x s g1)
addInsert = undefined

addTwice :: AddCtx x s g1 g2
         -> AddCtx y t g2 g3
         -> (AddCtx y t g1 (Insert y t g1), AddCtx x s (Insert y t g1) g3)
addTwice AddHere           (AddLater pfAdd)  = 
         case addInsert pfAdd of Dict -> (AddLater pfAdd, AddHere)
addTwice (AddLater pfAdd)   AddHere          = 
         case addInsert pfAdd of Dict -> (AddHere, AddLater pfAdd)
addTwice (AddLater pfAdd1) (AddLater pfAdd2) = 
         let (pfAdd1', pfAdd2') = addTwice pfAdd1 pfAdd2
         in (AddLater pfAdd1', AddLater pfAdd2')

-- Merge ----------------------------------------------------

-- merge g1 g2 g3
-- assuming g1 and g2 share a frame f, merge is functional.
data Merge :: Ctx -> Ctx -> Ctx -> * where
  MergeE  :: Merge '[] '[] '[]
  MergeEL :: Merge '[] g g
  MergeER :: Merge g '[] g
  MergeL :: Merge g1 g2 g3 
         -> Merge ('Used t ': g1) ('Unused ': g2) ('Used t ': g3)
  MergeR :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Used t ': g2) ('Used t ': g3)
  MergeU :: Merge g1 g2 g3 
         -> Merge ('Unused ': g1) ('Unused ': g2) ('Unused ': g3)


mergeEmpty3 :: forall g. EmptyCtx g -> Merge g g g
mergeEmpty3 EmptyNil = MergeE
mergeEmpty3 (EmptyCons pfEmpty) = MergeU (mergeEmpty3 pfEmpty)

mergeEmpty :: forall g1 g2 g. 
              Merge g1 g2 g 
           -> EmptyCtx g 
           -> (EmptyCtx g1, EmptyCtx g2)
mergeEmpty MergeE        EmptyNil       = (EmptyNil, EmptyNil)
mergeEmpty MergeEL       pfEmpty        = (EmptyNil, pfEmpty)
mergeEmpty MergeER       pfEmpty        = (pfEmpty, EmptyNil)
mergeEmpty (MergeU pfM) (EmptyCons pfE) = 
  let (pfE1, pfE2) = mergeEmpty pfM pfE 
  in (EmptyCons pfE1, EmptyCons pfE2)

type family Remove x g :: Ctx where
  Remove 'Z     (_ ': g) = g
  Remove ('S x) (u ': g) = u ': Remove x g


mergeAdd :: Merge g1 g2 g 
         -> AddCtx x s g0 g
         -> Either (AddCtx x s (Remove x g1) g1, Merge (Remove x g1) g2 g0)
                   (AddCtx x s (Remove x g2) g2, Merge g1 (Remove x g2) g0)
mergeAdd = undefined
