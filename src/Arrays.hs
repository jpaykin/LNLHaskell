{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
--             IncoherentInstances


module Arrays where
 
import Data.Kind
import qualified Data.Array.IO as ArrayIO
import Prelude hiding (read)
import Data.Proxy
import Data.Constraint

import Types
import Context
import Lang
import Subst
import Eval
import Interface
import Domain


-- Signature
-- ty will get substituted with (LType sig)
data ArraySig :: TypeSig where
  ArraySig :: * -> ArraySig ty


data ArrayLVal (val :: LType sig -> *) :: LType sig -> * where
  VArr    :: forall sig (val :: LType sig -> *) a. 
             HasArraySig sig => LArray sig a -> ArrayLVal val (Array sig a)

type ArrayDomain sig = (ArrayLVal :: Dom sig)  

-- Has Array type -----------------------------------------------

--class HasArrayType' flag sig where
--  type ArrayType sig flag (a :: *) = (r :: SigType sig (LType sig)) | r -> a 
class HasArrayType sig where
  pfHasArray :: Dict (HasArray sig ~ 'True)

--type family HasArray sig where
--  HasArray '(IO,ArraySig) = 'True
--  HasArray _ = 'False
--type family If (b :: Bool) a1 a2 where
--  If 'True  a1 a2 = a1
--  If 'False a1 a2 = a2
type family Array sig a = (r :: LType sig) | r -> a where
  Array '(IO,ArraySig) a = 'Sig ('ArraySig a)
--  Array '(m,sig1 :+: sig2) a = 
--    If (HasArray '(m,sig1)) ('Sig ('AndTy1 (Array '(m,sig1) a)))
--                            ('Sig ('AndTy2 (Array '(m,sig2) a)))
  Array '(IO,ArraySig :+: sig2) a = 'Sig ('AndTy1 (Array '(IO,ArraySig) a))
  Array '(m,sig1 :+: sig2) a = 'Sig ('AndTy2 (Array '(m,sig2) a))



-- instance HasArrayType' 0 sig => HasArrayType sig where
--   type Array sig a = 'Sig (ArrayType sig 0 a)

-- instance HasArrayType' flag '(IO,ArraySig) where
--   type ArrayType '(IO,ArraySig) _ a = 'ArraySig a

-- instance HasArrayType' 0 '(m,sig1) => HasArrayType' 1 '(m, sig1 :+: sig2) where
--   type ArrayType '(m, sig1 :+: sig2) 1 a = 'AndTy1 (ArrayType '(m,sig1) 0 a)

-- instance HasArrayType' 0 '(m,sig2) => HasArrayType' 2 '(m, sig1 :+: sig2) where
--   type ArrayType '(m, sig1 :+: sig2) 2 a = 'AndTy2 (ArrayType '(m,sig2) 0 a)

-- instance HasArrayType' 1 sig => HasArrayType' 0 sig where
--   type ArrayType sig 0 a = ArrayType sig 1 a
-- instance HasArrayType' 2 sig => HasArrayType' 0 sig where
--   type ArrayType sig 0 a = ArrayType sig 2 a


-- Has Array Signature ------------------------------------------

class Monad (SigEffect sig) => HasArraySig sig where
  type LArray sig (a :: *) = (r :: *) | r -> a

  newArray       :: Int -> a -> SigEffect sig (LArray sig a)
  readArray      :: LArray sig a -> Int -> SigEffect sig a
  writeArray     :: LArray sig a -> Int -> a -> SigEffect sig ()
  deallocArray   :: LArray sig a -> SigEffect sig ()


instance HasArraySig '(IO,ArraySig) where
  type LArray '(IO,ArraySig) a = ArrayIO.IOArray Int a

  newArray n     =  ArrayIO.newArray (0,n)
  readArray      =  ArrayIO.readArray
  writeArray     =  ArrayIO.writeArray
  deallocArray m =  return ()
  

--- Expressions -------------------------------------------
data ArrayLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  Alloc   :: forall sig a (exp :: Ctx sig -> LType sig -> *).
             Int -> a -> ArrayLExp exp 'Empty (Array sig a)
  Dealloc :: forall sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             exp g (Array sig a) -> ArrayLExp exp g One
  Read    :: forall  sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             Int -> exp g (Array sig a) -> ArrayLExp exp g (Array sig a ⊗ Lower a)
  Write   :: forall sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             Int -> exp g (Array sig a) -> a -> ArrayLExp exp g (Array sig a)
  Arr     :: forall sig a (exp :: Ctx sig -> LType sig -> *).
             LArray sig a -> ArrayLExp exp Empty (Array sig a)




class HasArraySig sig => HasArrays (dom :: Dom sig) where
  alloc   :: Int -> a -> LExp dom 'Empty (Array sig a)
  dealloc :: forall g a. LExp dom g (Array sig a) -> LExp dom g One
  read    :: Int -> LExp dom g (Array sig a) -> LExp dom g (Array sig a ⊗ Lower a)
  write   :: Int -> LExp dom g (Array sig a) -> a -> LExp dom g (Array sig a)
  array   :: LArray sig a -> LExp dom 'Empty (Array sig a)
  
  varray  :: LArray sig a -> LVal dom (Array sig a)
  


instance HasArraySig sig
--          Domain (ArrayDomain sig) ArrayLExp) 
       => HasArrays (ArrayDomain sig) where
  alloc n a   = Dom (Proxy :: Proxy ArrayLExp) $ Alloc n a
  dealloc e   = Dom (Proxy :: Proxy ArrayLExp) $ Dealloc e
  read i e    = Dom (Proxy :: Proxy ArrayLExp) $ Read i e
  write i e a = Dom (Proxy :: Proxy ArrayLExp) $ Write i e a
  array arr   = Dom (Proxy :: Proxy ArrayLExp) $ Arr arr

  varray arr  = VDom (Proxy :: Proxy ArrayLExp) $ VArr arr

instance HasArraySig sig => ToExp (ArrayDomain sig) ArrayLExp where
  valToExpDomain _ (VArr arr) = Arr arr

instance HasArraySig sig => Domain (ArrayDomain sig) ArrayLExp where

  substDomain _ pfA s (Dealloc e)   = dealloc $ subst pfA s e
  substDomain _ pfA s (Read i e)    = read    i $ subst pfA s e
  substDomain _ pfA s (Write i e a) = write   i (subst pfA s e) a

  evalDomain _ (Alloc n a) = do
    arr <- newArray @sig n a
    return $ varray arr
  evalDomain _ (Dealloc e) = do
    VDom _ (VArr arr) <- eval' e
    deallocArray @sig arr
    return VUnit
  -- evalDomain _ (Read i e) = do
  --   VDom _ (VArr arr) <- eval' e
  --   a <- readArray @sig arr i
  --   return $ varray arr `VPair` VPut a
  -- evalDomain _ (Write i e a) = do
  --   VDom _ (VArr arr) <- eval' e
  --   writeArray @sig arr i a
  --   return $ varray arr
  evalDomain _ (Arr arr) = return $ varray arr


-- Examples

liftApply :: Lift dom (a ⊸ b) -> Lift dom a -> Lift dom b
liftApply f a = Suspend $ force f `app` force a


fromList :: HasArrays (dom :: Dom sig) => [a] -> Lift dom (Array sig a)
fromList [] = error "Cannot call fromList on an empty list"
fromList ls@(a:as) = Suspend $ 
    force (fromList' 0 ls) `app` alloc len a
  where
    len = length ls

fromList' :: HasArrays (dom :: Dom sig) => Int -> [a] -> Lift dom (Array sig a ⊸ Array sig a)
fromList' offset []     = Suspend . λ $ \x -> var x
fromList' offset (a:as) = Suspend . λ $ \ arr -> 
  force (fromList' (1+offset) as) `app` write offset (var arr) a
--  write offset a `compose` fromList' (1+offset) as
    


toList :: HasArrays dom => Int -> Lift dom (Array sig a ⊸ Lower [a])
toList len = Suspend . λ $ \arr ->
--  force (toList' len) `letin` λ $ \f ->
  (force (toList' len) `app` var arr) `letPair` \(arr,ls) ->
  dealloc (var arr) `letUnit`
  var ls

toList' :: HasArrays dom => Int -> Lift dom (Array sig a ⊸ Array sig a ⊗ Lower [a])
toList' 0     = Suspend . λ $ \arr -> 
    var arr ⊗ put []
toList' i = Suspend . λ $ \arr ->
  read (i-1) (var arr) `letPair` \(arr,x) ->
  force (toList' (i-1)) `app` var arr `letPair` \(arr,xs) ->
  var x  >! \ a -> 
  var xs >! \as ->
  var arr ⊗ put (as ++ [a])


toFromList :: HasArrays dom => [a] -> Lin dom [a]
toFromList ls = suspendL $ 
  force (toList len) `app` (force $ fromList ls)
  where
    len = length ls

type MyArrayDomain = ArrayDomain '(IO,ArraySig)
main :: Lin MyArrayDomain [Int]
main = toFromList [1,2,3]
