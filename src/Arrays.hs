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
--import Domain


-- Signature
-- ty will get substituted with (LType sig)
data ArraySig :: TypeSig where
  ArraySig :: * -> ArraySig ty

{-
class CInList i ty sig => HasArrayType i (ty :: TypeSig) sig where
  type family Array' ty a = (r :: LType sig) | r -> a 

instance CInList i ArraySig sig => HasArrayType i ArraySig sig where
  type Array' ArraySig a = 'Sig PfInSig ('ArraySig a)
-}

type Array sig a = 'Sig (ArrayInList (SigType sig)) ('ArraySig a :: ArraySig (LType sig))

type family ArrayInList ty :: InList ArraySig ty where
  ArrayInList (ArraySig ': _) = 'InList 'InZ
  ArrayInList (_ ': ty)       = InListCons (ArrayInList ty)

type family InListCons (pf :: InList (x :: a) ls) :: InList x (y ': ls) where
  InListCons ('InList pfM) = 'InList ('InS pfM)

-- Array type family -----------------------------------------------
{-
type family Array sig a = (r :: LType sig) | r -> a where
  Array '(IO,ArraySig) a = 'Sig ('ArraySig a)
--  Array '(m,sig1 :+: sig2) a = 
--    If (HasArray '(m,sig1)) ('Sig ('AndTy1 (Array '(m,sig1) a)))
--                            ('Sig ('AndTy2 (Array '(m,sig2) a)))
  Array '(IO,ArraySig :+: sig2) a = 'Sig ('AndTy1 (Array '(IO,ArraySig) a))
  Array '(m,sig1 :+: sig2) a = 'Sig ('AndTy2 (Array '(m,sig2) a))
-}

-- Array Effect ----------------------------------------------------

--type family LArray m a = r | r -> a where
--  LArray IO a          = ArrayIO.IOArray Int a
type family LArray' sig a where
  LArray' sig a = LArray (SigEffect sig) a

class Monad m => HasArrayEffect m where
  type family LArray m a = r | r -> a
  newArray       :: Int -> a -> m (LArray m a)
  readArray      :: LArray m a -> Int -> m a
  writeArray     :: LArray m a -> Int -> a -> m ()
  deallocArray   :: LArray m a -> m ()

instance HasArrayEffect IO where
  type LArray IO a = ArrayIO.IOArray Int a
  newArray n     =  ArrayIO.newArray (0,n)
  readArray      =  ArrayIO.readArray
  writeArray     =  ArrayIO.writeArray
  deallocArray m =  return ()

class HasArrayEffect (SigEffect sig) => HasArraySig sig  


-- Has Array Domain ------------------------------------------

data ArrayLVal (val :: LType sig -> *) :: LType sig -> * where
  VArr    :: forall sig (val :: LType sig -> *) a. 
             HasArraySig sig => LArray' sig a -> ArrayLVal val (Array sig a)

{-

class HasArraySig sig => HasArrayDom (dom :: Dom sig) where
  varray  :: LArray' sig a -> LVal dom (Array sig a)

instance HasArraySig sig => HasArrayDom (ArrayDomain sig) where
  varray arr  = VDom (Proxy :: Proxy ArrayLExp) $ VArr arr
-}

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
             LArray' sig a -> ArrayLExp exp Empty (Array sig a)


class HasArraySig sig => HasArrayDom sig (dom :: Dom sig)

class (CInList i '(ArrayLExp, ArrayLVal) dom, HasArrayDom sig dom)
   => HasArrays i (dom :: Dom sig) where
  arrayInDom :: InMap i '(ArrayLExp,ArrayLVal) dom

instance (HasArrayDom sig dom, CInList i '(ArrayLExp, ArrayLVal) dom)
   => HasArrays i dom where
  arrayInDom = pfInList 

fromArrayLExp :: forall i sig (dom :: Dom sig) g t.
                 HasArrays i dom => ArrayLExp (LExp dom) g t -> LExp dom g t
fromArrayLExp = Dom (arrayInDom @i) 

-- As long as the HasArrays instance is the only source of Array values, 
-- this function is total.
lValToArray :: forall i sig (dom :: Dom sig) a.
               HasArrays i dom
            => LVal dom (Array sig a) -> ArrayLVal (LVal dom) (Array sig a)
lValToArray (VDom pfInList' v) = 
  case compareInList (pfInList @_ @i @'(ArrayLExp,ArrayLVal)) pfInList' of
    Nothing   -> error "Value of type Array a not derived from Arrays class"
    Just Dict -> v
--lValToArray _ = error "Value of type Array a not derived from Arrays class"

alloc :: forall i sig (dom :: Dom sig) a.
         HasArrays i dom
      => Int -> a -> LExp dom 'Empty (Array sig a)
alloc n a = Dom (arrayInDom @i) $ Alloc n a

dealloc :: forall i sig (dom :: Dom sig) g a.
           HasArrays i dom
        => LExp dom g (Array sig a) -> LExp dom g One
dealloc = fromArrayLExp @i . Dealloc

read :: forall i sig (dom :: Dom sig) g a.
        HasArrays i dom
     => Int -> LExp dom g (Array sig a) -> LExp dom g (Array sig a ⊗ Lower a)
read i e = fromArrayLExp @i $ Read i e

write :: forall i sig (dom :: Dom sig) g a.
        HasArrays i dom
     => Int -> LExp dom g (Array sig a) -> a -> LExp dom g (Array sig a)
write i e a = fromArrayLExp @i $ Write i e a 

array :: forall i sig (dom :: Dom sig) g a.
        HasArrays i dom
     => LArray' sig a -> LExp dom 'Empty (Array sig a)
array = fromArrayLExp @i . Arr

varray :: forall i sig (dom :: Dom sig) g a.
        HasArrays i dom
     => LArray' sig a -> LVal dom (Array sig a)
varray = VDom (arrayInDom @i) . VArr


instance HasArrays i dom
      => Domain i ArrayLExp ArrayLVal (dom :: Dom sig) where

  valToExpDomain _ (VArr arr) = Arr arr

  substDomain _ pfA s (Dealloc e)   = dealloc @i $ subst pfA s e
  substDomain _ pfA s (Read i e)    = read    @i i $ subst pfA s e
  substDomain _ pfA s (Write i e a) = write   @i i (subst pfA s e) a

  evalDomain _ (Alloc n a) = do
    arr <- newArray @(SigEffect sig) n a
    return $ varray @i arr
  evalDomain _ (Dealloc e) = do
    VArr arr <- fmap (lValToArray @i) $ eval' e
    deallocArray @(SigEffect sig) arr
    return VUnit
  evalDomain _ (Read i e) = do
    VArr arr <- fmap (lValToArray @i) $ eval' e
    a <- readArray @(SigEffect sig) arr i
    return $ varray @i arr `VPair` VPut a
  evalDomain _ (Write i e a) = do
    VArr arr <- fmap (lValToArray @i) $ eval' e
    writeArray @(SigEffect sig) arr i a
    return $ varray @i arr
  evalDomain _ (Arr arr) = return $ varray @i arr


-- Examples


liftApply :: Lift dom (a ⊸ b) -> Lift dom a -> Lift dom b
liftApply f a = Suspend $ force f `app` force a


fromList :: forall i sig (dom :: Dom sig) a.
            HasArrays i dom => [a] -> Lift dom (Array sig a)
fromList [] = error "Cannot call fromList on an empty list"
fromList ls@(a:as) = Suspend $ 
    force (fromList' @i 0 ls) `app` alloc @i len a
  where
    len = length ls

fromList' :: forall i sig (dom :: Dom sig) a.
             HasArrays i dom
          => Int -> [a] -> Lift dom (Array sig a ⊸ Array sig a)
fromList' offset []     = Suspend . λ $ \x -> var x
fromList' offset (a:as) = Suspend . λ $ \ arr -> 
  force (fromList' @i (1+offset) as) `app` write @i offset (var arr) a


toList :: forall i sig (dom :: Dom sig) a.
          HasArrays i dom => Int -> Lift dom (Array sig a ⊸ Lower [a])
toList len = Suspend . λ $ \arr ->
  (force (toList' @i len) `app` var arr) `letPair` \(arr,ls) ->
  dealloc @i (var arr) `letUnit`
  var ls

toList' :: forall i sig (dom :: Dom sig) a.
           HasArrays i dom 
        => Int -> Lift dom (Array sig a ⊸ Array sig a ⊗ Lower [a])
toList' 0     = Suspend . λ $ \arr -> 
    var arr ⊗ put []
toList' i = Suspend . λ $ \arr ->
  read @i (i-1) (var arr) `letPair` \(arr,x) ->
  force (toList' @i (i-1)) `app` var arr `letPair` \(arr,xs) ->
  var x  >! \ a -> 
  var xs >! \as ->
  var arr ⊗ put (as ++ [a])


toFromList :: forall i dom a. HasArrays i dom => [a] -> Lin dom [a]
toFromList ls = suspendL $ 
  force (toList @i len) `app` (force $ fromList @i ls)
  where
    len = length ls

type MyArraySig = ( '(IO, '[ ArraySig ]) :: Sig )
instance HasArraySig MyArraySig

type MyArrayDomain = ( '[ '(ArrayLExp,ArrayLVal) ] :: Dom MyArraySig )
instance HasArrayDom MyArraySig MyArrayDomain

main :: Lin MyArrayDomain [Int]
main = toFromList @'Z [1,2,3]

