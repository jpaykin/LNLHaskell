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
import System.TimeIt
import Control.Monad (void)

import Types
import Context
import Lang
import Interface
--import Domain


-- Signature
-- ty will get substituted with (LType sig)
data ArraySig :: TypeSig where
  ArraySig :: * -> ArraySig ty

type Array a = ('Sig (InSig ArraySig sig) ('ArraySig a) :: LType sig)

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

data ArrayLVal (lang :: Lang sig) :: LType sig -> * where
  VArr    :: forall sig (lang :: Lang sig) a. 
             LArray' sig a -> ArrayLVal lang (Array a)

--- Expressions -------------------------------------------
data ArrayLExp (lang :: Lang sig) :: Ctx sig -> LType sig -> * where
  Alloc   :: Int -> a -> ArrayLExp lang 'Empty (Array a)
  Dealloc :: LExp lang g (Array a) -> ArrayLExp lang g One
  Read    :: Int -> LExp lang g (Array a) -> ArrayLExp lang g (Array a ⊗ Lower a)
  Write   :: Int -> LExp lang g (Array a) -> a -> ArrayLExp lang g (Array a)
--  Arr     :: forall sig a (lang :: Lang sig).
--             LArray' sig a -> ArrayLExp lang Empty (Array a)

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
       Domain TensorDom lang, Domain LowerDom lang, Domain LolliDom lang)
   => HasArrayDom (lang :: Lang sig) 
instance (HasArraySig sig, Domain OneDom lang, Domain ArrayDom lang, 
       Domain TensorDom lang, Domain LowerDom lang, Domain LolliDom lang)
   => HasArrayDom (lang :: Lang sig) 

alloc :: HasArrayDom lang
      => Int -> a -> LExp lang 'Empty (Array a)
alloc n a = Dom proxyArray $ Alloc n a

allocL :: HasArrayDom lang
       => Int -> a -> Lift lang (Array a)
allocL n a = Suspend $ alloc n a

dealloc :: HasArrayDom lang
        => LExp lang g (Array a) -> LExp lang g One
dealloc = Dom proxyArray . Dealloc

deallocL :: HasArrayDom lang
         => Lift lang (Array a ⊸ One)
deallocL = Suspend . λ $ \ arr -> dealloc $ var arr

read :: HasArrayDom lang
     => Int -> LExp lang g (Array a) -> LExp lang g (Array a ⊗ Lower a)
read i e = Dom proxyArray $ Read i e

readM :: HasArrayDom lang
      => Int -> LinT lang (LState' (Array a)) a
readM i = suspendT . λ $ \arr -> read i $ var arr

write :: HasArrayDom lang
     => Int -> LExp lang g (Array a) -> a -> LExp lang g (Array a)
write i e a = Dom proxyArray $ Write i e a 

writeM :: forall sig (lang :: Lang sig) a.
          HasArrayDom lang
       => Int -> a -> LinT lang (LState' (Array a)) ()
writeM i a = suspendT . λ $ \arr -> write i (var arr) a ⊗ put ()


varray :: forall sig (lang :: Lang sig) a.
        HasArrayDom lang
     => LArray' sig a -> LVal lang (Array a)
varray = VDom proxyArray . VArr


instance HasArrayDom lang
      => Language ArrayDom lang where

  evalDomain _ (Alloc n a) = do
    arr <- newArray n a
    return $ varray arr
  evalDomain ρ (Dealloc e) = do
    VArr arr <- evalToValDom proxyArray ρ e
    deallocArray arr
    return vunit
  evalDomain ρ (Read i e) = do
    VArr arr <- evalToValDom proxyArray ρ e
    a <- readArray arr i
    return $ varray arr `vpair` vput a
  evalDomain ρ (Write i e a) = do
    VArr arr <- evalToValDom proxyArray ρ e
    writeArray arr i a
    return $ varray arr

-- Examples

fromList :: HasArrayDom lang
         => [a] -> Lift lang (Array a)
fromList [] = error "Cannot call fromList on an empty list"
fromList ls@(a:as) = execLState (fromListSt 0 ls) (allocL (length ls) a)

fromListSt :: HasArrayDom lang
           => Int -> [a] -> LinT lang (LState' (Array a)) ()
fromListSt offset [] = return ()
fromListSt offset (a:as) = do
  writeM offset a
  fromListSt (offset+1) as


toList :: HasArrayDom lang 
       => Int -> Lift lang (Array a) -> Lin lang [a]
toList i arr = evalLState (toList' i) arr deallocL

toList' :: HasArrayDom lang
        => Int -> LinT lang (LState' (Array a)) [a]
toList' 0 = return []
toList' i = do
  a  <- readM (i-1)
  as <- toList' (i-1)
  return $ as ++ [a]

toFromList :: HasArrayDom lang
           => [a] -> Lin lang [a]
toFromList ls = toList (length ls) $ fromList ls

type MyArraySig = ( '(IO, '[ ArraySig, TensorSig, OneSig, LowerSig, LolliSig ]) :: Sig)
type MyArrayDom = ( 'Lang '[ ArrayDom, TensorDom, OneDom, LowerDom, LolliDom ] :: Lang MyArraySig )


toFromListIO :: [a] -> Lin MyArrayDom [a]
toFromListIO = toFromList

--main :: IO [Int]
--main = run mainL


-- Compare to plain IOArrays

-- Invoke with the length of the array
toListPlain :: Int -> LArray IO a -> IO [a]
toListPlain 0 _ = return []
toListPlain i arr = do
  a <- readArray arr (i-1)
  as <- toListPlain (i-1) arr
  return $ as ++ [a]
  
fromListPlain :: [a] -> IO (LArray IO a)
fromListPlain [] = error "Cannot call fromList on an empty list"
fromListPlain ls@(a:as) = do
  arr <- newArray (length ls) a
  fromListPlain' 0 ls arr
  return arr

fromListPlain' :: Int -> [a] -> LArray IO a -> IO ()
fromListPlain' offset [] _ = return ()
fromListPlain' offset (a:as) arr = do
  writeArray arr offset a
  fromListPlain' (offset+1) as arr

toFromListPlain :: [a] -> IO [a]
toFromListPlain ls = do
  arr <- fromListPlain ls
  toListPlain (length ls) arr

plain :: IO [Int]
plain = toFromListPlain $ replicate 1000 3

comp :: Int -> IO ()
comp n = do
  timeIt . void . run $ toFromListIO ls
  timeIt . void $ toFromListPlain ls
  where
    ls = replicate n 3


{-




type MyArraySig = ( '(IO, '[ ArraySig ]) :: Sig )

type MyArrayDomain = ( '[ ArrayDom ] :: Dom MyArraySig )

main :: Lin MyArrayDomain [Int]
main = toFromList @'Z [1,2,3]
-}
