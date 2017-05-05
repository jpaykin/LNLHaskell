{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds, LambdaCase,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
--             IncoherentInstances


module Arrays where
 
import Data.Kind
import qualified Data.Array.IO as IO
import Prelude hiding (read, (^), drop)
import qualified Prelude as Prelude
import Data.Proxy
import Data.List (insert)
import Data.Constraint
import System.TimeIt
import Control.Monad (void, foldM, forM_)
import Debug.Trace
import Control.Monad.State.Lazy (State(..), runState)
import Control.Concurrent.MVar
import Control.Concurrent


import Types
--import Context
import Interface
import Classes
import ShallowEmbedding

data ExistsArray f α where 
  ExistsArray :: f (Array token α) -> ExistsArray f α

-- Signature
data ArraySig sig = ArraySig Type Type
type Array token a = MkLType ('ArraySig token a)

class HasMILL sig => HasArray sig where
  alloc   :: Int -> α -> ExistsArray (LExp sig Empty) α
  drop    :: LExp sig γ (Array token a) -> LExp sig γ One
  slice   :: Int -> LExp sig γ (Array token a) -> LExp sig γ (Array token a ⊗ Array token a)
  join    :: CMerge γ1 γ2 γ 
          => LExp sig γ1 (Array token α) -> LExp sig γ2 (Array token α) 
          -> LExp sig γ (Array token α)
  read    :: Int -> LExp sig γ (Array token a) -> LExp sig γ (Array token a ⊗ Lower a)
  write   :: Int -> LExp sig γ (Array token a) -> a -> LExp sig γ (Array token a)
  scope   :: LExp sig γ (Array token a) -> LExp sig γ (Array token a ⊗ Lower [Int])

type instance Effect Shallow = IO
-- a VArray has a list of variables in scope as well as a primitive array
data instance LVal Shallow (Array token a) = VArray [Int] (IO.IOArray Int a)

instance HasArray Shallow where
  alloc n a = ExistsArray $ SExp $ \_ -> VArray [0..n-1] <$> IO.newArray (0,n) a
  drop e = SExp $ \γ -> runSExp e γ >> return VUnit
  slice i e = SExp $ \γ -> do 
        VArray bounds arr <- runSExp e γ
        return $ VPair ( VArray (filter (< i) bounds) arr )
                       ( VArray (filter (>= i) bounds) arr )
  join e1 e2 = SExp $ \γ -> do  let (γ1,γ2) = split γ
                                v1 <- newEmptyMVar
                                v2 <- newEmptyMVar
                                forkIO $ runSExp e1 γ1 >>= putMVar v1
                                forkIO $ runSExp e2 γ2 >>= putMVar v2
                                VArray bounds1 arr <- takeMVar v1
                                VArray bounds2 arr <- takeMVar v2
                                return $ VArray (mergeList bounds1 bounds2) arr
  read i e = SExp $ \γ -> do
        VArray bounds arr <- runSExp e γ
        if i `elem` bounds then do
            a <- IO.readArray arr i
            return $ VPair (VArray bounds arr) (VPut a)
        else error $ "Read " ++ show i ++ " out of bounds " ++ show bounds
  write i e a = SExp $ \γ -> do
        VArray bounds arr <- runSExp e γ
        if i `elem` bounds then do
            IO.writeArray arr i a
            return $ VArray bounds arr
        else error $ "Write " ++ show i ++ " out of bounds " ++ show bounds
  scope e = SExp $ \γ -> do
        VArray bounds arr <- runSExp e γ
        return $ VPair (VArray bounds arr) (VPut bounds)

-- mergeList takes in two sorted lists, and produces a sorted list
mergeList :: [Int] -> [Int] -> [Int]
mergeList = foldr insert
--mergeList [] ls = ls
--mergeList ls [] = ls
--mergeList (a1:ls1) (a2:ls2) = if a1 <= a2 then a1 : mergeList ls1 (a2:ls2)
--                              else a2 : mergeList (a1:ls1) ls2

readT :: HasArray sig => Int -> LinT sig (LState' (Array token a)) a
readT i = suspend . λ $ read i

writeT :: HasArray sig => Int -> a -> LinT sig (LState' (Array token a)) ()
writeT i a = suspend . λ $ \arr -> write i arr a ⊗ put ()

scopeT :: HasArray sig => LinT sig (LState' (Array token a)) [Int]
scopeT = suspend . λ $ scope

sliceT :: HasArray sig
       => Int 
       -> LStateT sig (Array token α) ()
       -> LStateT sig (Array token α) ()
       -> LStateT sig (Array token α) ()
sliceT i st1 st2 = -- trace ("slicing at index " ++ show i) $ 
                   suspend . λ $ \arr ->
                   slice i arr `letPair` \(arr1,arr2) ->
                   force st1 ^ arr1 `letPair` \(arr1,res) -> res >! \_ ->
                   force st2 ^ arr2 `letPair` \(arr2,res) -> res >! \_ ->
                   join arr1 arr2 ⊗ put ()

quicksort :: (HasArray sig,Ord α) 
          => LStateT sig (Array token α) ()
quicksort = partition >>= \case Nothing -> return ()
                                Just p  -> sliceT p quicksort quicksort
    

--     bounds <- scopeT
-- --    trace ("calling quicksort on bounds " ++ show bounds) $
--     if length bounds > 1 
--     then do let lo = head bounds
--                 hi = last bounds
--             p <- partition bounds
--             if (lo < p) && (p < hi) 
--               then sliceT p quicksort quicksort
--               else return ()
--     else return ()

partition :: (HasArray sig,Ord α) 
          => LStateT sig (Array token α) (Maybe Int)
partition = scopeT >>= \case -- if the domain of the array has length <= 1, return -1
                [] -> return Nothing
                [_] -> return Nothing
                (lo:bounds) -> do p <- readT lo
                                  (lastclosed,i) <- pivot (lo:bounds) p
                                  swap lo lastclosed
                                  return $ Just i
                

-- partition bounds = do -- trace ("partitioning on bounds " ++ show bounds) $ do 
--                       let lo = head bounds
--                       p <- readT lo
--                       (lastclosed,i) <- pivot (bounds) p
-- --                      trace ("pivot = " ++ show i) $ do
--                       swap lo lastclosed
--                       return $ i

pivot :: forall sig α token. (HasArray sig,Ord α)
      => [Int] -> α -> LStateT sig (Array token α) (Int,Int)
pivot (i:bounds) p = do
    (lastclosed,open) <- foldM f (i,[]) bounds 
    return (lastclosed,head open)
  where
    f :: (Int,[Int]) -> Int -> LStateT sig (Array token α) (Int,[Int]) 
    f (lastclosed,open) j = do 
        let newopen = open ++ [j] -- first open j
        b <- readT j -- lookup the value of j
        if b < p 
          then do let close = head newopen
                  swap j close
                  return (close, tail newopen)
          else return (lastclosed, newopen)

swap :: HasArray sig => Int -> Int -> LStateT sig (Array token α) ()
swap i j = do -- trace ("swapping indices " ++ show i ++ " and " ++ show j) $ do 
              a <- readT i
              b <- readT j
              writeT i b
              writeT j a

test :: Lin Shallow [Int]
test = evalArrayList quicksort [3,1,4,1,5,9,2,6,5,3]


-- Fold -----------------------------------

sizeT :: HasArray sig => LStateT sig (Array token α) Int
sizeT = do bounds <- scopeT
           return $ length bounds

        
foldArrayT :: HasArray sig
            => (a -> b -> b)
            -> b -> LinT sig (LState' (Array token a)) b
foldArrayT f b = do
    bounds <- scopeT
    foldM f' b bounds
  where
    f' b i = do
        a <- readT i
        return $ f a b

toListT :: HasArray sig => LinT sig (LState' (Array token a)) [a]
toListT = foldArrayT snoc []
  where
    snoc a ls = ls ++ [a]

fromList :: forall sig a. HasArray sig => [a] -> ExistsArray (Lift sig) a
fromList ls = case alloc (length ls) (head ls) of 
    ExistsArray new -> ExistsArray $ 
      foldr (execLStateT . f) (suspend new) $ zip ls [0..]
  where
    f :: (a,Int) -> LStateT sig (Array token a) ()
    f (a,i) = writeT i a



evalArrayState :: HasArray sig
               => (forall token. LinT sig (LState' (Array token a)) b) 
               -> ExistsArray (Lift sig) a -> Lin sig b
evalArrayState st (ExistsArray arr) = evalLStateT st arr (suspend . λ $ drop)

evalArrayList :: HasArray sig
              => (forall token. LStateT sig (Array token α) β) 
              -> [α] -> Lin sig [α]
evalArrayList st ls = evalArrayState (st >> toListT) (fromList ls)

toFromList :: [a] -> Lin Shallow [a]
toFromList ls = evalArrayState toListT (fromList ls)

myArray :: ExistsArray (Lift Shallow) String
myArray = case alloc 2 "hello" of { ExistsArray new -> ExistsArray $
    execLStateT foo $ suspend new
  }
  where
    foo :: LStateT Shallow (Array token String) ()
    foo = writeT 1 "world"
myArrayToList :: Lin Shallow ([String],[Int])
myArrayToList = evalArrayState st' myArray 
  where
    st' = do arr <- toListT
             bounds <- scopeT
             return $ (arr,bounds)
    

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
--    ls <- run $ toFromList [3,5,2]
--    putStrLn $ "Test: " ++ show ls
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
