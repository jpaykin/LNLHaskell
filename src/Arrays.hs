{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts
#-}

module Arrays where
 
import Data.Kind
import qualified Data.Array.IO as ArrayIO
import Prelude hiding (read)

import Types
import Lang
import Subst
import Eval

-- Signature
data ArraySig ty where
  ArraySig :: * -> ArraySig ty

type Array a = Sig ('ArraySig a)

-- Domain specification
type ArrayEffect = IO
type LArray a = ArrayIO.IOArray Int a
newArray       :: Int -> a -> IO (LArray a)
newArray n     =  ArrayIO.newArray (0,n)
readArray      :: LArray a -> Int -> IO a
readArray      =  ArrayIO.readArray
writeArray     :: LArray a -> Int -> a -> IO ()
writeArray     =  ArrayIO.writeArray
deallocArray   :: LArray a -> IO ()
deallocArray m =  return ()



data ArrayLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  Alloc   :: Int -> a -> ArrayLExp exp 'Empty (Array a)
  Dealloc :: exp g (Array a) -> ArrayLExp exp g One
  Read    :: Int -> exp g (Array a) -> ArrayLExp exp g (Array a ⊗ Lower a)
  Write   :: Int -> exp g (Array a) -> a -> ArrayLExp exp g (Array a)
  Arr     :: LArray a -> ArrayLExp exp Empty (Array a)


data ArrayLVal (val :: LType sig -> *) :: LType sig -> * where
  VArr    :: LArray a -> ArrayLVal val (Array a)

type ArrayDomain = '(IO,'(ArrayLExp,ArrayLVal))

class HasArrays dom where
  alloc   :: Int -> a -> LExp dom 'Empty (Array a)
  dealloc :: LExp dom g (Array a) -> LExp dom g One
  read    :: Int -> LExp dom g (Array a) -> LExp dom g (Array a ⊗ Lower a)
  write   :: Int -> LExp dom g (Array a) -> a -> LExp dom g (Array a)

instance HasArrays ArrayDomain where
  alloc n a   = Dom $ Alloc n a
  dealloc e   = Dom $ Dealloc e
  read i e    = Dom $ Read i e
  write i e a = Dom $ Write i e a



instance Domain ArrayDomain where

  toExpDomain (VArr arr) = Arr arr
  
  substDomain pfA s (Dealloc e) = dealloc $ subst pfA s e
  substDomain pfA s (Read i e)  = read i $ subst pfA s e
  substDomain pfA s (Write i e a) = write i (subst pfA s e) a
  
  evalDomain (Alloc n a) = do
    arr <- newArray n a
    return $ VDom (VArr arr)
  evalDomain (Dealloc e) = do
    VDom (VArr arr) <- eval' e
    () <- deallocArray arr
    return VUnit
  evalDomain (Read i e) = do
    v@(VDom (VArr arr)) <- eval' e
    a <- readArray arr i
    return $ v `VPair` VPut a
  evalDomain (Write i e a) = do
    v@(VDom (VArr arr)) <- eval' e
    () <- writeArray arr i a
    return v




