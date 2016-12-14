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
import Interface


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



data ArrayLExp (exp :: Ctx ArraySig -> LType ArraySig -> *) :: Ctx ArraySig -> LType ArraySig -> * where
  Alloc   :: Int -> a -> ArrayLExp exp 'Empty (Array a)
  Dealloc :: exp g (Array a) -> ArrayLExp exp g One
  Read    :: Int -> exp g (Array a) -> ArrayLExp exp g (Array a ⊗ Lower a)
  Write   :: Int -> exp g (Array a) -> a -> ArrayLExp exp g (Array a)
  Arr     :: LArray a -> ArrayLExp exp Empty (Array a)


data ArrayLVal (val :: LType ArraySig -> *) :: LType ArraySig -> * where
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
  evalDomain (Arr arr) = return . VDom $ VArr arr



-- Examples

liftApply :: Lift dom (a ⊸ b) -> Lift dom a -> Lift dom b
liftApply f a = Suspend $ force f `app` force a


fromList :: [a] -> Lift ArrayDomain (Array a)
fromList [] = error "Cannot call fromList on an empty list"
fromList ls@(a:as) = Suspend $ 
    force (fromList' 0 ls) `app` alloc len a
  where
    len = length ls

fromList' :: Int -> [a] -> Lift ArrayDomain (Array a ⊸ Array a)
fromList' offset []     = Suspend . λ $ \x -> var x
fromList' offset (a:as) = Suspend . λ $ \ arr -> 
  force (fromList' (1+offset) as) `app` write offset (var arr) a
--  write offset a `compose` fromList' (1+offset) as
    



toList :: Int -> Lift ArrayDomain (Array a ⊸ Lower [a])
toList len = Suspend . λ $ \arr ->
--  force (toList' len) `letin` λ $ \f ->
  (force (toList' len) `app` var arr) `letPair` \(arr,ls) ->
  dealloc (var arr) `letUnit`
  var ls

toList' :: Int -> Lift ArrayDomain (Array a ⊸ Array a ⊗ Lower [a])
toList' 0     = Suspend . λ $ \arr -> 
    var arr ⊗ put []
toList' i = Suspend . λ $ \arr ->
  read (i-1) (var arr) `letPair` \(arr,x) ->
  force (toList' (i-1)) `app` var arr `letPair` \(arr,xs) ->
  var x  >! \ a -> 
  var xs >! \as ->
  var arr ⊗ put (as ++ [a])
  
toFromList :: [a] -> Lin ArrayDomain [a]
toFromList ls = suspendL $ 
  force (toList len) `app` (force $ fromList ls)
  where
    len = length ls

