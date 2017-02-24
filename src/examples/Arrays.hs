{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
--             IncoherentInstances


module Arrays where
 
import Data.Kind
import qualified Data.Array.IO as IO
import Prelude hiding (read, (^))
import qualified Prelude as Prelude
import Data.Proxy
import Data.Constraint
import System.TimeIt
import Control.Monad (void, foldM, forM_)
import Debug.Trace
import Control.Monad.State.Lazy (State(..), runState)

-- this implementation is really slow

import Types
--import Context
import Interface
import ShallowEmbedding

-- Signature
data ArraySig sig = ArraySig Type
type Array a = MkLType ('ArraySig a)

class HasMILL sig => HasArray sig where
  alloc   :: Int -> a -> LExp sig Empty (Array a)
  dealloc :: LExp sig γ (Array a) -> LExp sig γ One
  read    :: Int -> LExp sig γ (Array a) -> LExp sig γ (Array a ⊗ Lower a)
  write   :: Int -> LExp sig γ (Array a) -> a -> LExp sig γ (Array a)
  size    :: LExp sig γ (Array a) -> LExp sig γ (Array a ⊗ Lower Int)

type instance Effect Shallow = IO
data instance LVal Shallow (Array a) = VArray (IO.IOArray Int a)

instance HasArray Shallow where
  alloc n a = SExp $ \_ -> VArray <$> IO.newArray (0,n) a
  dealloc (SExp e) = SExp $ \γ -> e γ >> return VUnit
  read i (SExp e) = SExp $ \γ -> do
        VArray arr <- e γ
        a <- IO.readArray arr i
        return $ VPair (VArray arr) (VPut a)
  write i (SExp e) a = SExp $ \γ -> do
        VArray arr <- e γ
        IO.writeArray arr i a
        return $ VArray arr
  size (SExp e) = SExp $ \γ -> do
        VArray arr <- e γ
        (low,high) <- IO.getBounds arr
        return $ VPair (VArray arr) (VPut $ high-low)

readT :: HasArray sig => Int -> LinT sig (LState' (Array a)) a
readT i = suspend . λ $ read i

writeT :: HasArray sig => Int -> a -> LinT sig (LState' (Array a)) ()
writeT i a = suspend . λ $ \arr -> write i arr a ⊗ put ()

sizeT :: HasArray sig => LinT sig (LState' (Array a)) Int
sizeT = suspend . λ $ size

-- Fold



-- foldrArray :: HasArray sig
--            => Lift sig (Lower a ⊸ τ ⊸ τ) 
--            -> LExp sig 'Empty (τ ⊸ Array a ⊸ Array a ⊗ τ)
-- foldrArray f = λ $ \seed -> λ $ \arr -> 
--     size arr `letPair` \(arr,l) -> l >! \len ->
--     foldrArray' len f `app` seed `app` arr
--   where
--     foldrArray' :: HasArrayDom lang
--                 => Int -> Lift lang (Lower a ⊸ τ ⊸ τ)
--                 -> LExp lang 'Empty (τ ⊸ Array a ⊸ Array a ⊗ τ)
--     foldrArray' 0 f = λ $ \seed -> λ $ \arr -> arr ⊗ seed
--     foldrArray' n f = λ $ \seed -> λ $ \arr ->
--         read (n-1) arr `letPair` \(arr,v) ->
--         foldrArray' (n-1) f `app` (force f `app` v `app` seed) `app` arr
        

foldArrayT :: HasArray sig
            => (a -> b -> b)
            -> b -> LinT sig (LState' (Array a)) b
foldArrayT f b = do
    n <- sizeT
    foldM f' b [0..n-1]
  where
    f' b i = do
        a <- readT i
        return $ f a b

toListT :: HasArray sig => LinT sig (LState' (Array a)) [a]
toListT = foldArrayT (:) []


fromList :: forall sig a. HasArray sig => [a] -> Lift sig (Array a)
fromList ls = foldr (execLStateT . f) (suspend . alloc (length ls) $ head ls) $ zip ls [0..]
  where
    f :: (a,Int) -> LinT sig (LState' (Array a)) ()
    f (a,i) = writeT i a



evalArrayState :: HasArray sig
               => LinT sig (LState' (Array a)) b -> Lift sig (Array a) -> Lin sig b
evalArrayState st a = evalLStateT st a (suspend . λ $ dealloc)

toFromList :: [a] -> Lin Shallow [a]
toFromList ls = evalArrayState toListT (fromList ls)


-------------------------------
-- Compare to plain IOArrays --
-------------------------------

foldArrayIO :: (a -> b -> b) -> b -> IO.IOArray Int a -> IO b
foldArrayIO f b arr = do
    (low,high) <- IO.getBounds arr
    foldM f' b [low..high]
  where
    f' b i = do
        a <- IO.readArray arr i
        return $ f a b

toListIO :: IO.IOArray Int a -> IO [a]
toListIO = foldArrayIO (:) []

fromListIO :: forall a. [a] -> IO (IO.IOArray Int a)
fromListIO ls = do
    arr <- IO.newArray_ (0,length ls)
    mapM_ (f' arr) $ zip ls [0..]
    return arr
  where
    f' :: IO.IOArray Int a -> (a,Int) -> IO ()
    f' arr (a,i) = IO.writeArray arr i a

fromListIO' :: forall a. [a] -> IO (IO.IOArray Int a)
fromListIO' ls = IO.newListArray (0,length ls-1) ls

toFromListIO :: [a] -> IO [a]
--toFromListIO ls = fromListIO ls >>= toListIO
toFromListIO ls = fromListIO' ls >>= IO.getElems

compareIO :: Int -> IO ()
compareIO n = do
    print $ "Calling toFromList on a list of size " ++ show n
    putStr "Linear:\t"
    timeIt . void . run $ toFromList ls
    putStr "Direct:\t"
    timeIt . void $ toFromListIO ls
  where
    ls = replicate n 10



compareUpTo :: Int -> IO ()
compareUpTo n = forM_ ls compareIO 
  where
    ls = ((Prelude.^) 2) <$> [0..n]
