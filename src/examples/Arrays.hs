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
import Data.List (insert, sort)
import Data.Constraint
import System.TimeIt
import Control.Monad (void, foldM, forM_, replicateM_)
import Debug.Trace
import Control.Monad.State.Lazy (State(..), runState)
import Control.Concurrent.MVar
import Control.Concurrent
import System.Random (randomRIO)



import Types
import Interface
import Classes
import ShallowEmbedding

data ExistsArray f α where 
  ExistsArray :: f (Array token α) -> ExistsArray f α

-- Signature
data ArraySig sig = ArraySig Type Type
type Array token a = MkLType ('ArraySig token a)

class HasMILL sig => HasArray sig where
  alloc   :: Int -> α -> ExistsArray (LExp sig '[]) α
  drop    :: LExp sig γ (Array token a) -> LExp sig γ One
  slice   :: (Int -> Bool) 
          -> LExp sig γ (Array token a) 
          -> LExp sig γ (Array token a ⊗ Array token a)
  join    :: CMerge γ1 γ2 γ 
          => LExp sig γ1 (Array token α) 
          -> LExp sig γ2 (Array token α) 
          -> LExp sig γ (Array token α)
  read    :: Int -> LExp sig γ (Array token a) -> LExp sig γ (Array token a ⊗ Lower a)
  write   :: Int -> LExp sig γ (Array token a) -> a -> LExp sig γ (Array token a)
  scope   :: LExp sig γ (Array token a) -> LExp sig γ (Array token a ⊗ Lower [Int])

type instance Effect Shallow = IO
-- a VArray has a list of variables in scope as well as a primitive array
data instance LVal Shallow (Array token a) = VArray [Int] (IO.IOArray Int a)

instance HasArray Shallow where -- NOTE: bounds of newArray are inclusive!
  alloc n a = ExistsArray $ SExp $ \_ -> VArray [0..n-1] <$> IO.newArray (0,n-1) a
  drop e = SExp $ \γ -> runSExp e γ >> return VUnit
  slice cond e = SExp $ \γ -> do 
        VArray bounds arr <- runSExp e γ
        return $ VPair ( VArray (filter cond bounds) arr )
                       ( VArray (filter (not . cond) bounds) arr )
  join e1 e2 = SExp $ \γ -> do  let (γ1,γ2) = split γ
                                VArray bounds1 arr <- runSExp e1 γ1
                                VArray bounds2 _   <- runSExp e2 γ2 
                                return $ VArray (mergeList bounds1 bounds2) arr
--   join e1 e2 = SExp $ \γ -> do  let (γ1,γ2) = split γ
--                                 v1 <- newEmptyMVar
--                                 v2 <- newEmptyMVar
--                                 forkIO $ runSExp e1 γ1 >>= putMVar v1
--                                 forkIO $ runSExp e2 γ2 >>= putMVar v2
--                                 VArray bounds1 arr <- takeMVar v1
--                                 VArray bounds2 arr <- takeMVar v2
-- --                              return $ VArray (bounds1 ++ bounds2) arr
--                                 return $ VArray (mergeList bounds1 bounds2) arr

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
  scope e = SExp $ \γ -> do -- Always return a sorted list of bounds
                            -- alternative to keeping the bounds sorted
                            -- via mergeList in join
        VArray bounds arr <- runSExp e γ
        return $ VPair (VArray bounds arr) (VPut $ bounds)

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

{-
  sliceT takes as input:
    cond :: Int -> Bool 
    state1, state2 ::  LStateT sig (Array token α) ()
  and will apply state1 on 'filter cond bound'
  and will apply state2 on 'filter (\x -> not (cond x)) bound'
-}    
sliceT :: HasArray sig
       => (Int -> Bool)
       -> LStateT sig (Array token α) ()
       -> LStateT sig (Array token α) ()
       -> LStateT sig (Array token α) ()
sliceT cond st1 st2 = -- trace ("slicing at index " ++ show i) $ 
                   suspend . λ $ \arr ->
                   slice cond arr `letPair` \(arr1,arr2) -> 
                   force st1 ^ arr1 `letPair` \(arr1,res) -> res >! \_ ->
                   force st2 ^ arr2 `letPair` \(arr2,res) -> res >! \_ ->
                   join arr1 arr2 ⊗ put ()


quicksort :: (HasArray sig,Ord α) 
          => LStateT sig (Array token α) ()
quicksort = partition >>= \case Nothing -> return ()
                                Just p  -> sliceT (<p) quicksort $
                                           sliceT (>p) quicksort $ 
                                           return ()
    
-- for documentation, see partitionIO
partition :: forall sig α token. (HasArray sig,Ord α) 
          => LStateT sig (Array token α) (Maybe Int)
partition = scopeT >>= \case -- if the domain of the array has length <= 1
                []        -> return Nothing
                [_]       -> return Nothing
                lo:bounds -> do p <- readT lo
                                boundsGT <- foldM (pivot1 p) [] bounds
                                let boundsLE = if null boundsGT
                                               then bounds
                                               else let minGT = head boundsGT
                                                    in filter (<minGT) bounds
                                let maxLE = if null boundsLE
                                            then lo
                                            else last boundsLE
                                swap lo maxLE
                                return $ Just maxLE
  where
    pivot1 :: α -> [Int] -> Int -> LStateT sig (Array token α) [Int]
    pivot1 p boundsGT j = do
        b ← readT j
        if b > p
        then return $ boundsGT ++ [j]
        else case boundsGT of
               [] -> return []
               x:boundsGT' -> swap x j >> return boundsGT'


swap :: HasArray sig => Int -> Int -> LStateT sig (Array token α) ()
swap i j = do -- trace ("swapping indices " ++ show i ++ " and " ++ show j) $ do 
              a <- readT i
              b <- readT j
              writeT i b
              writeT j a

test' :: Lin Shallow [Int]
test' = evalArrayList quicksort [3,1,4,1,5,9,2,6,5,3]

test :: [Int] -> Lin Shallow [Int]
test ls = evalArrayList quicksort ls


-- Fold -----------------------------------

sizeT :: HasArray sig => LStateT sig (Array token α) Int
sizeT = do bounds <- scopeT
           return $ length bounds

        
foldArrayT :: HasArray sig
            => (a -> b -> (a,b))
            -> b -> LinT sig (LState' (Array token a)) b
foldArrayT f b = do
    bounds <- scopeT
    foldM f' b bounds
  where
    f' b i = do
        a <- readT i
        let (a',b') = f a b
        writeT i a'
        return b'

toListT :: HasArray sig => LinT sig (LState' (Array token a)) [a]
toListT = foldArrayT (\a b -> (a,snoc a b)) []
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

-- testFold n 
-- applies a successor function n times to a list of all 0's that has length 100.
testFold :: Int -> Lin Shallow [Int]
testFold n = evalArrayList (replicateM_ n $ foldArrayT (\i b -> (i+1,b)) False) $ replicate 100 0
    

-------------------------------
-- Compare to plain IOArrays --
-------------------------------

foldArrayIO :: (a -> b -> (a,b)) -> b -> IO.IOArray Int a -> IO b
foldArrayIO f b arr = do
    (low,high) <- IO.getBounds arr
    foldM f' b [low..high]
  where
    f' b i = do
        a <- IO.readArray arr i
        let (a',b') = f a b
        IO.writeArray arr i a'
        return $ b'

toListIO :: IO.IOArray Int a -> IO [a]
toListIO = foldArrayIO (\ a b -> (a,snoc a b)) []
  where
    snoc a ls = ls ++ [a]

fromListIO :: forall a. [a] -> IO (IO.IOArray Int a)
fromListIO ls = do
    arr <- IO.newArray_ (0,length ls-1)
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





quicksortIO :: Ord α => IO.IOArray Int α -> [Int] -> IO ()
quicksortIO arr bounds = partitionIO arr bounds >>= \case
                            Nothing -> return ()
                            Just i  -> let bounds1 = filter (< i) bounds
                                           bounds2 = filter (> i) bounds
                                       in do quicksortIO arr bounds1
                                             quicksortIO arr bounds2

-- In partitionIO arr bounds, we assume that 'bounds' is 
-- a sorted list of indices into the arrray
-- The result will be None if |bounds|<=1
-- Otherwise, partitionIO arr bounds will pick a pivot value
-- and return Just mid
-- so that after the function call, 
--      arr[mid]=pivot
--      ∀ i ∈ bounds, if i <= mid then arr[i] <= pivot
--                and if i > mid then arr[i] > pivot
partitionIO :: forall α. Ord α => IO.IOArray Int α -> [Int] -> IO (Maybe Int)
partitionIO arr []          = return Nothing
partitionIO arr [_]         = return Nothing
partitionIO arr (lo:bounds) = do 
    p ← IO.readArray arr lo
    boundsGT <- foldM (pivot1 p) [] bounds
    -- arr = [p] ++ boundsLE ++ boundsGT
    -- first, compute boundsLE
    let boundsLE = if null boundsGT 
                   then bounds
                   else let minGT = head boundsGT
                        in filter (<minGT) bounds
    -- we need to swap p with the last element in boundsLE,
    -- which is the largest bound that is less than 
    -- the minimum element in boundsGT
    -- if boundsLE=[] then just swap lo with itself
    let maxLE = if null boundsLE
                then lo
                else last boundsLE
    swapIO arr lo maxLE
    return $ Just maxLE

  where
    {-
        The condition isSplit(arr,boundsGT) says that
        the array 'arr' has the form:
            arr = arrLE ++ arrGT ++ unassessed
        where bounds(arrLE)      = ?
              bounds(arrGT)      = boundsGT
        and ∀ i ∈ arrLE, arr[i] <= pivot
            ∀ j ∈ arrGT, arr[j] > pivot

        For pivot1(pivot,boundsGT,j) = boundsGT'
        Precondition: isSplit(arr,boundsGT)
        Postcondition: isSplit(arr,boundsGT')

        If Arr[j] <= p: 
            pivot1 p [] j : boundsLE ++ [] ++ [j] ++ unassessed 
                        ==> (boundsLE ++ j) ++ [] ++ unassessed
            pivot1 p (x:boundsGT) j : boundsLE ++ (x>p) ++ boundsGT ++ (j<=p)
                        ==>           (boundsLE ++ x) ++ (boundsGT ++ j)
                        AKA swap x and j
        If Arr[j] > p:
            pivot1 p boundsGT j : boundsLE ++ boundsGT ++ (j>p) ++ unassessed
                              ==> boundsLE ++ (boundsGT ++ j) ++ unassessed
    -}      
    pivot1 :: α -> [Int] -> Int -> IO [Int]
    pivot1 p boundsGT j = do
        b ← IO.readArray arr j
        if b > p
        then return $ boundsGT ++ [j]
        else case boundsGT of
               [] -> return []
               (x:boundsGT) -> swapIO arr x j >> return boundsGT


swapIO :: Ord α => IO.IOArray Int α -> Int -> Int -> IO ()
swapIO arr i j = do a ← IO.readArray arr i
                    b ← IO.readArray arr j
                    IO.writeArray arr i b
                    IO.writeArray arr j a



-- expect: [1,1,2,3,3,4,5,5,6,9]
testIO :: [Int] -> IO [Int]
testIO ls = do arr <- fromListIO ls
               (lo,hi) <- IO.getBounds arr
               quicksortIO arr [lo..hi]
               toListIO arr

testIO' :: IO [Int]
testIO' = testIO [3,1,4,1,5,9,2,6,5,3]

testFoldIO :: Int -> IO [Int]
testFoldIO n = do arr <- fromListIO $ replicate 100 0
                  replicateM_ n $ foldArrayIO (\i b -> (i+1,b)) False arr
                  toListIO arr



-- Comparison --

compareQuicksort :: Int -> IO ()
compareQuicksort n = do
    print $ "Calling quicksort on a list of size " ++ show n
    ls <- randomList n
    seq ls $ return ()
    putStr "Linear:\t"
    timeIt . void . run $ test ls
    putStr "Direct:\t"
    timeIt . void $ testIO ls

compareFold :: Int -> IO ()
compareFold n = do
    print $ "Calling fold " ++ show n ++ " times"
    putStr "Linear:\t"
    timeIt . void . run $ testFold n
    putStr "Direct:\t"
    timeIt . void $ testFoldIO n
    

randomList :: Int -> IO([Int])
randomList 0 = return []
randomList n = do
  r  <- randomRIO (1,100)
  rs <- randomList (n-1)
  return (r:rs) 


compareUpTo :: Int -> IO ()
--compareUpTo n = forM_ ls compareFold
compareUpTo n = forM_ ls compareQuicksort
  where
    ls = ((Prelude.^) 2) <$> [0..n]
--    ls = [1..n]

