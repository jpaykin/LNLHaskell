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
import Interface
--import Domain


-- Signature
-- ty will get substituted with (LType sig)
data ArraySig :: TypeSig where
  ArraySig :: * -> ArraySig ty

type Array a = ('Sig (IsInList ArraySig (SigType sig)) 
                     ('ArraySig a :: ArraySig (LType sig)) :: LType sig)

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
instance HasArrayEffect (SigEffect sig) => HasArraySig sig


-- Has Array Domain ------------------------------------------

data ArrayLVal (val :: LType sig -> *) :: LType sig -> * where
  VArr    :: forall sig (val :: LType sig -> *) a. 
             LArray' sig a -> ArrayLVal val (Array a)

--- Expressions -------------------------------------------
data ArrayLExp (exp :: Ctx sig -> LType sig -> *) :: Ctx sig -> LType sig -> * where
  Alloc   :: forall sig a (exp :: Ctx sig -> LType sig -> *).
             Int -> a -> ArrayLExp exp 'Empty (Array a)
  Dealloc :: forall sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             exp g (Array a) -> ArrayLExp exp g One
  Read    :: forall  sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             Int -> exp g (Array a) -> ArrayLExp exp g (Array a ⊗ Lower a)
  Write   :: forall sig a (exp :: Ctx sig -> LType sig -> *) (g :: Ctx sig).
             Int -> exp g (Array a) -> a -> ArrayLExp exp g (Array a)
  Arr     :: forall sig a (exp :: Ctx sig -> LType sig -> *).
             LArray' sig a -> ArrayLExp exp Empty (Array a)

type ArrayDom = '(ArrayLExp,ArrayLVal)

proxyArray :: Proxy ArrayDom
proxyArray = Proxy

{-
fromArrayLExp :: forall i sig (dom :: Dom sig) g t.
                 HasArrays i dom => ArrayLExp (LExp dom) g t -> LExp dom g t
fromArrayLExp = Dom $ pfInList @_ @i @ArrayDom

fromArrayLVal :: forall i sig (dom :: Dom sig) g t.
                 HasArrays i dom => ArrayLVal (LVal dom) t -> LVal dom t
fromArrayLVal = VDom $ pfInList @_ @i @ArrayDom
-}

{-
-- As long as the HasArrays instance is the only source of Array values, 
-- this function is total.
lValToArray :: forall i sig (dom :: Dom sig) a.
               HasArrays i dom
            => LVal dom (Array a) -> ArrayLVal (LVal dom) (Array a)
lValToArray (VDom pfInList' v) = 
  case compareInList (pfInList @_ @i @ArrayDom) pfInList' of
    Nothing   -> error "Value of type Array a not derived from Arrays class"
    Just Dict -> v
--lValToArray _ = error "Value of type Array a not derived from Arrays class"
-}

class (HasArraySig sig, Domain OneDom lang, Domain ArrayDom lang, 
       Domain TensorDom lang, Domain LowerDom lang)
   => HasArrayDom (lang :: Lang sig) 
instance (HasArraySig sig, Domain OneDom lang, Domain ArrayDom lang, 
       Domain TensorDom lang, Domain LowerDom lang)
   => HasArrayDom (lang :: Lang sig) 

alloc :: HasArrayDom lang
      => Int -> a -> LExp lang 'Empty (Array a)
alloc n a = Dom proxyArray $ Alloc n a

dealloc :: HasArrayDom lang
        => LExp lang g (Array a) -> LExp lang g One
dealloc = Dom proxyArray . Dealloc

read :: HasArrayDom lang
     => Int -> LExp lang g (Array a) -> LExp lang g (Array a ⊗ Lower a)
read i e = Dom proxyArray $ Read i e

write :: HasArrayDom lang
     => Int -> LExp lang g (Array a) -> a -> LExp lang g (Array a)
write i e a = Dom proxyArray $ Write i e a 

array :: forall sig (lang :: Lang sig) a.
         HasArrayDom lang
      => LArray' sig a -> LExp lang 'Empty (Array a)
array = Dom proxyArray . Arr

varray :: forall sig (lang :: Lang sig) a.
        HasArrayDom lang
     => LArray' sig a -> LVal lang (Array a)
varray = VDom proxyArray . VArr


instance HasArrayDom lang
      => Language ArrayDom lang where

  valToExpDomain _ (VArr arr) = Arr arr

  substDomain _ pfA s (Dealloc e)   = dealloc $ subst pfA s e
  substDomain _ pfA s (Read i e)    = read    i $ subst pfA s e
  substDomain _ pfA s (Write i e a) = write   i (subst pfA s e) a

  evalDomain _ (Alloc n a) = do
    arr <- newArray n a
    return $ varray arr
  evalDomain _ (Dealloc e) = do
    Just (VArr arr) <- fmap (fromLVal proxyArray) $ eval' e
    deallocArray arr
    return vunit
  evalDomain _ (Read i e) = do
    Just (VArr arr) <- fmap (fromLVal proxyArray) $ eval' e
    a <- readArray arr i
    return $ varray arr `vpair` vput a
  evalDomain _ (Write i e a) = do
    Just (VArr arr) <- fmap (fromLVal proxyArray) $ eval' e
    writeArray arr i a
    return $ varray arr
  evalDomain _ (Arr arr) = return $ varray arr

-- Examples


{-
liftApply :: Lift dom (a ⊸ b) -> Lift dom a -> Lift dom b
liftApply f a = Suspend $ force f `app` force a


fromList :: forall i sig (dom :: Dom sig) a.
            HasArrays i dom => [a] -> Lift dom (Array a)
fromList [] = error "Cannot call fromList on an empty list"
fromList ls@(a:as) = Suspend $ 
    force (fromList' @i 0 ls) `app` alloc @i len a
  where
    len = length ls

fromList' :: forall i sig (dom :: Dom sig) a.
             HasArrays i dom
          => Int -> [a] -> Lift dom (Array a ⊸ Array a)
fromList' offset []     = Suspend . λ $ \x -> var x
fromList' offset (a:as) = Suspend . λ $ \ arr -> 
  force (fromList' @i (1+offset) as) `app` write @i offset (var arr) a


toList :: forall i sig (dom :: Dom sig) a.
          HasArrays i dom => Int -> Lift dom (Array a ⊸ Lower [a])
toList len = Suspend . λ $ \arr ->
  (force (toList' @i len) `app` var arr) `letPair` \(arr,ls) ->
  dealloc @i (var arr) `letUnit`
  var ls

toList' :: forall i sig (dom :: Dom sig) a.
           HasArrays i dom 
        => Int -> Lift dom (Array a ⊸ Array a ⊗ Lower [a])
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

type MyArrayDomain = ( '[ ArrayDom ] :: Dom MyArraySig )

main :: Lin MyArrayDomain [Int]
main = toFromList @'Z [1,2,3]
-}
