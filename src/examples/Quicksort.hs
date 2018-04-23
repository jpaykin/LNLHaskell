module Quicksort where

-- import Data.Kind
import qualified Data.Array.IO as IO
import Prelude hiding (read, (^), drop)
import qualified Prelude as Prelude
-- import Data.Proxy
-- import Data.List (insert, sort)
-- import Data.Constraint
import System.TimeIt
import Control.Monad (void, forM_)
import Debug.Trace
-- import Control.Monad.State.Lazy (State(..), runState)
-- import Control.Concurrent.MVar
-- import Control.Concurrent
import System.Random (randomRIO)

import Test.QuickCheck
import qualified Test.QuickCheck.Monadic as QCM


-- import Types
import Interface
-- import Classes
import ShallowEmbedding
import Arrays
import Range

slice3 :: (HasArray sig, Show α)
       => Int
       -> LStateT sig (Array token α) ()
       -> LStateT sig (Array token α) ()
slice3 i op = -- apply op on indices < i and indices > i, do nothing at index i
      do len <- sizeT
         slice3' len 
  where
    slice3' len | len <= 2 = return ()
                | i == 0   = sliceT 1 (return ()) op
                | i == len-1 = sliceT i op (return ())
                | otherwise  = sliceT i op $ sliceT 1 (return ()) op
         -- if i == 0 then sliceT 1 (return ()) op
         -- else if i == len-1 then sliceT i op (return ())
         -- else sliceT i op $ sliceT 1 (return ()) op



quicksort :: (HasArray sig,Ord α, Show α) 
          => LStateT sig (Array token α) ()
quicksort = do len <- sizeT
               if len <= 1 then return () 
               else do p <- readT 0 -- get pivot element
                       idx <- partition p (1,len-1)
                       swap 0 idx
                       slice3 idx quicksort

-- partition pivot (i,j) 
-- assumes all indices less than i in the array are < pivot
-- and all indices greater than j in the array are >= pivot
-- so we are working our way in
-- if i = j, then we're done, and return i
-- otherwise, if arr[i] < pivot: recurse on (i+1,j)
-- otherwise, if arr[i] >= pivot: swap indices i and j, recurse on (i,j-1)
partition :: (HasArray sig, Ord α)
          => α -> Range -> LStateT sig (Array token α) Int
partition pivot (i,j) | i >= j    = do a <- readT i
                                       if a < pivot then return i else return (i-1)
                      | otherwise = do a <- readT i
                                       if a < pivot then partition pivot (i+1,j)
                                       else do swap i j
                                               partition pivot (i,j-1)


swap :: HasArray sig => Int -> Int -> LStateT sig (Array token α) ()
swap i j = do --trace ("swapping indices " ++ show i ++ " and " ++ show j) $ do 
              a <- readT i
              b <- readT j
              writeT i b
              writeT j a


quicksortTest :: [Int] -> IO [Int]
quicksortTest ls = run @Shallow $ evalArrayList quicksort ls 

outputTest :: [Int] -> IO [Int]
outputTest ls = run @Shallow $ evalArrayList (return ()) ls

testOp :: HasArray sig => LStateT sig (Array token Int) ()
testOp = do quicksort
            a <- readT 1
            trace (show a) $ return ()
-- testOp = do a <- readT 0
--             idx <- partition a (1,3) 
-- --            swap 0 idx
--             return idx
--quicksortTest :: Lin Shallow [Int]
--quicksortTest = evalArrayList testOp [1,4,2,-1,8,-4]

isSorted :: Ord α => [α] -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (a:b:as) = a <= b && isSorted (b:as)

quicksortProperty :: [Int] -> IO Bool
quicksortProperty ls = do ls <- run @Shallow $ evalArrayList quicksort ls
                          return $ isSorted ls

quicksortQuickcheck :: [Int] -> Property
quicksortQuickcheck ls = QCM.monadicIO $ QCM.run $ quicksortProperty ls

-------------------------------
-- Compare to plain IOArrays --
-------------------------------

data MyIOArray a = MyIOArray { getArray  :: IO.IOArray Int a
                             , getRSet :: RSet }

myAlloc :: Int -> α -> IO (MyIOArray α)
myAlloc n a = do arr <- IO.newArray (0,n-1) a
                 return $ MyIOArray arr [(0,n-1)]

mySlice :: Int -> MyIOArray α -> (MyIOArray α, MyIOArray α)
mySlice i (MyIOArray arr rs) = 
  if i < sizeRSet rs then let x = offsetRSet i rs
                              (rs1,rs2) = splitRSet x rs
                           in (MyIOArray arr rs1, MyIOArray arr rs2)
  else error $ "Slice " ++ show i ++ " out of bounds of " ++ show rs

mySliceT :: Int -> (MyIOArray α -> IO ()) ->
                   (MyIOArray α -> IO ()) ->
                   MyIOArray α -> IO ()
mySliceT i st1 st2 arr = 
    let (arr1,arr2) = mySlice i arr
    in st1 arr1 >> st2 arr2

mySlice3 :: Int -> (MyIOArray α -> IO ()) -> MyIOArray α -> IO ()
mySlice3 i op arr = let len = mySize arr
                    in mySlice3' len
  where 
    mySlice3' len | len <= 2   = return ()
                  | i == 0     = mySliceT 1 (\_ -> return ()) op arr
                  | i == len-1 = mySliceT i op (\_ -> return ()) arr
                  | otherwise  = mySliceT i op (mySliceT 1 (\_ -> return ()) op) arr

myRead :: Int -> MyIOArray α -> IO α
myRead i arr = if i < mySize arr then do let x = offsetRSet i rs
                                         IO.readArray (getArray arr) x
               else error $ "Read " ++ show i ++ " out of bounds of " ++ show rs
  where rs = getRSet arr


myWrite :: Int -> MyIOArray α -> α -> IO ()
myWrite i arr a = if i < mySize arr then do let x = offsetRSet i rs
                                            IO.writeArray (getArray arr) x a
                  else error $ "Write " ++ show i ++ " out of bounds " ++ show rs
  where rs = getRSet arr

mySize :: MyIOArray α -> Int
mySize arr = sizeRSet (getRSet arr)


foldArrayIO :: (a -> b -> b) -> b -> MyIOArray a -> IO b
foldArrayIO f b arr = do foldArrayIO' (mySize arr) f b
  where
    foldArrayIO' n f b | n <= 0    = return b
                       | otherwise = do b' <- foldArrayIO' (n-1) f b
                                        a <- myRead (n-1) arr
                                        return $ f a b'


toListIO :: MyIOArray a -> IO [a]
toListIO = foldArrayIO (\a ls -> ls ++ [a]) []

fromListIO :: forall a. [a] -> IO (MyIOArray a)
fromListIO ls = do arr <- myAlloc (length ls) (head ls)
                   fromListIO' 0 ls arr
                   return arr
  where
    fromListIO' :: Int -> [a] -> MyIOArray a -> IO ()
    fromListIO' _ []     _   = return ()
    fromListIO' i (a:ls) arr = myWrite i arr a >> fromListIO' (i+1) ls arr

runArrayIOList :: (MyIOArray α -> IO β) -> [α] -> IO ([α],β)
runArrayIOList op ls = do arr <- fromListIO ls
                          b   <- op arr
                          ls  <- toListIO arr
                          return (ls,b)
evalArrayIOList :: (MyIOArray α -> IO β) -> [α] -> IO [α]
evalArrayIOList op ls = do (ls,_) <- runArrayIOList op ls
                           return ls

swapIO :: Ord α => MyIOArray α -> Int -> Int -> IO ()
swapIO arr i j = do a ← myRead i arr
                    b ← myRead j arr
                    myWrite i arr b
                    myWrite j arr a

partitionIO :: Ord α
            => α -> Range -> MyIOArray α -> IO Int
partitionIO pivot (i,j) arr 
            | i >= j    = do a <- myRead i arr
                             if a < pivot then return i else return (i-1)
            | otherwise = do a <- myRead i arr
                             if a < pivot then partitionIO pivot (i+1,j) arr
                             else do swapIO arr i j
                                     partitionIO pivot (i,j-1) arr

quicksortIO :: Ord α
            => MyIOArray α -> IO ()
quicksortIO arr = do let len = mySize arr
                     if len <= 1 then return ()
                     else do p <- myRead 0 arr
                             idx <- partitionIO p (1,len-1) arr
                             swapIO arr 0 idx
                             mySlice3 idx quicksortIO arr

--quicksortIOTest :: IO [Int]
--quicksortIOTest = evalArrayIOList quicksortIO [1,4,2,-1,8,-4] 

quicksortIOProperty :: [Int] -> IO Bool
quicksortIOProperty ls = do ls' <- evalArrayIOList quicksortIO ls
                            return $ isSorted ls'
quicksortIOQuickcheck :: [Int] -> Property
quicksortIOQuickcheck ls = QCM.monadicIO $ QCM.run $ quicksortIOProperty ls

quicksortIOTest :: [Int] -> IO [Int]
quicksortIOTest ls = evalArrayIOList quicksortIO ls 

outputIOTest :: [Int] -> IO [Int]
outputIOTest ls = evalArrayIOList (\_ -> return ()) ls

-- Comparison --

compareQuicksort :: Int -> IO ()
compareQuicksort n = do
    print $ "Calling quicksort on a list of size " ++ show n
    ls <- randomList n
    seq ls $ return ()
    putStr "Direct:\t"
    timeIt . void $ quicksortIOTest ls
    putStr "Linear:\t"
    timeIt . void $ quicksortTest ls


randomList :: Int -> IO([Int])
randomList 0 = return []
randomList n = do
  r  <- randomRIO (1,100)
  rs <- randomList (n-1)
  return (r:rs) 

compareOutputList :: Int -> IO ()
compareOutputList n = do
    print $ "Outputting a list of size " ++ show n
    ls <- randomList n
    seq ls $ return ()
    putStr "Linear:\t"
    timeIt . void $ outputTest ls
    putStr "Direct:\t"
    timeIt . void $ outputIOTest ls


compareUpTo :: Int -> IO ()
compareUpTo n = forM_ ls compareQuicksort -- compareOutputList
  where
    ls = ((Prelude.^) 2) <$> [0..n]
--    ls = [1..n]
