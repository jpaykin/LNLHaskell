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

-- Fresh variable ------------------------------------------

type family Fresh g :: Ident where
  Fresh '[] = 'Z
  Fresh ('Unused ': g) = 'Z
  Fresh ('Used s ': g) = 'S (Fresh g)

type family Fresh2 g :: Ident where
  Fresh2 '[] = 'S 'Z
  Fresh2 ('Unused ': g) = 'S (Fresh g)
  Fresh2 ('Used s ': g) = 'S (Fresh2 g)

-- Disjoint Identifiers --------------------------------

data Disjoint :: Ident -> Ident -> * where
  DisjointZS :: Disjoint 'Z ('S n) 
  DisjointSZ :: Disjoint ('S n) 'Z
  DisjointSS :: Disjoint m n -> Disjoint ('S m) ('S n)

-- Shift -----------------------------------------------------

data ShiftN :: Ident -> NCtx -> NCtx -> * where
  ShiftHere  :: ShiftN 'Z g ('Cons 'Unused g)
  ShiftLater :: ShiftN x g g' -> ShiftN ('S x) ('Cons u g) ('Cons u' g)

data Shift :: Nat -> Ctx -> Ctx -> * where
  Shift :: ShiftN x g g' -> Shift x ('N g) ('N g')


-- Add To Context ----------------------------------------------

data AddCtxN :: Ident -> LType -> Ctx -> NCtx -> * where
  AddEHere   :: AddCtxN 'Z s 'Empty ('End s)
  AddHere    :: AddCtxN 'Z s ('N ('Cons 'Unused g)) ('Cons ('Used s) g)
  AddELater  :: AddCtxN x s 'Empty g  -> AddCtxN ('S x) s 'Empty ('Cons 'Unused g)
  AddLater   :: AddCtxN x s ('N g) g' -> AddCtxN ('S x) s ('N ('Cons u g)) ('Cons u g')

data AddCtx  :: Nat -> LType -> Ctx -> Ctx -> * where
  AddN :: AddCtxN x s g g' -> AddCtx x s g ('N g')


-- Singleton Context ------------------------------------------

data SingletonNCtx :: Nat -> LType -> NCtx -> * where
  AddHereS  :: SingletonNCtx 'Z s ('End s)
  AddLaterS :: SingletonNCtx x s g -> SingletonNCtx ('S x) s ('Cons 'Unused g)

data SingletonCtx :: Nat -> LType -> Ctx -> * where
  SingN :: SingletonNCtx x s g -> SingletonCtx x s ('N g)


-- Merge ----------------------------------------------------

data MergeU :: Usage -> Usage -> Usage -> * where
  MergeUn :: MergeU 'Unused   'Unused   'Unused
  MergeUL :: MergeU ('Used s) 'Unused   ('Used s)
  MergeUR :: MergeU 'Unused   ('Used s) ('Used s)

data Merge :: Ctx -> Ctx -> Ctx -> * where
  MergeE  :: Merge 'Empty 'Empty 'Empty
  MergeEL :: Merge 'Empty ('N g) ('N g)
  MergeER :: Merge ('N g) 'Empty ('N g)
  MergeN  :: MergeN g1 g2 g3 -> Merge ('N g1) ('N g2) ('N g3)

data MergeN :: NCtx -> NCtx -> NCtx -> * where
  MergeEndL :: MergeN ('End s) ('Cons 'Unused g2) ('Cons ('Used s) g2)
  MergeEndR :: MergeN ('Cons 'Unused g1) ('End s) ('Cons ('Used s) g1)
  MergeCons :: MergeU u1 u2 u3 -> MergeN g1 g2 g3 
            -> MergeN ('Cons u1 g1) ('Cons u2 g2) ('Cons u3 g3)


-- Remove ------------------------------------------


-- In -------------------------------

data In :: Nat -> LType -> NCtx -> * where
  InEnd   :: In 'Z s ('End s)
  InHere  :: SNCtx g   -> In 'Z s ('Cons ('Used s) g)
  InLater :: In x s g  -> In ('S x) s ('Cons u g)

-- Relation between In and Shift

type family InShift x n :: Nat where
  InShift ('S x) 'Z     = x
  InShift 'Z     ('S n) = 'Z
  InShift ('S x) ('S n) = 'S (InShift x n)


