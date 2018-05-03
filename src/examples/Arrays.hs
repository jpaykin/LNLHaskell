module Arrays where
 
import Data.Kind
import qualified Data.Array.IO as IO
import Prelude hiding (read, (^), drop)
-- import qualified Prelude as Prelude
import Data.Proxy
-- import Data.List (insert, sort)
-- import Data.Constraint
-- import Control.Monad (void, foldM, forM_, replicateM_)
-- import Debug.Trace
-- import Control.Monad.State.Lazy (State(..), runState)
-- import Control.Concurrent.MVar
-- import Control.Concurrent
-- import System.Random (randomRIO)
-- import GHC.TypeLits
-- import Test.QuickCheck

import Types
import Interface
import Classes
import ShallowEmbedding
import Range

-- Signature
data ArraySig exp = ArraySig Type Type
type Array token a = MkLType ('ArraySig token a)

class HasMILL exp => HasArray exp where
  alloc   :: ( CAddCtx x (Array token α) γ γ'
             , CSingletonCtx x (Array token α) γ''
             , x ~ Fresh γ)
          => Int -> α 
          -> (exp γ'' (Array token α) -> exp γ' σ)
          -> exp γ σ
  dealloc :: exp γ (Array token a) -> exp γ One
  slice   :: Int 
          -> exp γ (Array token a) 
          -> exp γ (Array token a ⊗ Array token a)
  join    :: CMerge γ1 γ2 γ 
          => exp γ1 (Array token α) 
          -> exp γ2 (Array token α) 
          -> exp γ (Array token α)
  read    :: Int -> exp γ (Array token a) 
          -> exp γ (Array token a ⊗ Lower a)
  write   :: Int -> exp γ (Array token a) -> a -> exp γ (Array token a)
  size    :: exp γ (Array token a) -> exp γ (Array token a ⊗ Lower Int)
--ranges  :: exp γ (Array token α) -> exp γ (Array token α ⊗ Lower [Range])

type instance Effect Shallow = IO


                 

-- a VArray has a list of ranges in scope as well as a primitive array
newtype instance LVal Shallow (Array token a) = VArray ([Range],IO.IOArray Int a)


instance HasArray Shallow where -- NOTE: bounds of newArray are inclusive!
  alloc   :: forall x token γ γ' γ'' α σ.
             ( CAddCtx x (Array token α) γ γ'
             , CSingletonCtx x (Array token α) γ''
             , x ~ Fresh γ)
          => Int -> α 
          -> (Shallow γ'' (Array token α) -> Shallow γ' σ)
          -> Shallow γ σ
  alloc n a k = SExp $ \γ -> do 
        arr <- IO.newArray (0,n-1) a
        let v = (VArray ([(0,n-1)],arr) :: LVal Shallow (Array token α))
            x = (Proxy :: Proxy x) 
        runSExp (k $ var x) (addECtx x v γ)
  dealloc e = SExp $ \γ -> runSExp e γ >> return (VUnit ())

  slice i e = SExp $ \γ -> do 
    VArray (rs,arr) <- runSExp e γ 
    if i < sizeRSet rs then let x = offsetRSet i rs
                                (rs1,rs2) = splitRSet x rs
                            in return $ VPair (VArray (rs1,arr), VArray (rs2,arr))
    else error $ "Slice " ++ show i ++ " out of bounds of " ++ show rs


  join e1 e2 = SExp $ \γ -> do  let (γ1,γ2) = splitECtx γ
                                VArray (rs1,arr) <- runSExp e1 γ1
                                VArray (rs2,_)   <- runSExp e2 γ2 
                                return $ VArray (mergeRSet rs1 rs2, arr)
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
        VArray (rs,arr) <- runSExp e γ
        if i < sizeRSet rs then do let x = offsetRSet i rs
                                   a <- IO.readArray arr x
                                   return $ VPair (VArray (rs,arr), VPut a)
        else error $ "Read " ++ show i ++ " out of bounds of " ++ show rs

  write i e a = SExp $ \γ -> do
        VArray (rs,arr) <- runSExp e γ
        if i < sizeRSet rs then do let x = offsetRSet i rs
                                   IO.writeArray arr x a
                                   return $ VArray (rs,arr)
        else error $ "Write " ++ show i ++ " out of bounds " ++ show rs

  size e = SExp $ \γ -> do VArray (rs,arr) <- runSExp e γ
                           let n = sizeRSet rs
                           return $ VPair (VArray (rs,arr), VPut n)

--  ranges e = SExp $ \γ -> do VArray (rs,arr) <- runSExp e γ
--                             return $ VPair (VArray (rs,arr), VPut rs)



readT :: HasArray exp => Int -> LinT exp (LState' (Array token a)) a
readT i = suspend . λ $ read i

writeT :: HasArray exp => Int -> a -> LinT exp (LState' (Array token a)) ()
writeT i a = suspend . λ $ \arr -> write i arr a ⊗ put ()


sizeT :: HasArray exp => LStateT exp (Array token α) Int
sizeT = suspend . λ $ \arr -> size arr

--rangesT :: HasArray exp => LStateT exp (Array token α) [Range]
--rangesT = suspend . λ $ \arr -> ranges arr




{-
  sliceT takes as input:
    cond :: Int -> Bool 
    state1, state2 ::  LStateT exp (Array token α) ()
  and will apply state1 on 'filter cond bound'
  and will apply state2 on 'filter (\x -> not (cond x)) bound'
-}    
sliceT :: HasArray exp
       => Int
       -> LStateT exp (Array token α) ()
       -> LStateT exp (Array token α) ()
       -> LStateT exp (Array token α) ()
sliceT i st1 st2 = -- trace ("slicing at index " ++ show i) $ 
                   suspend . λ $ \arr ->
                     slice i arr `letPair` \(arr1,arr2) -> 
                     force st1 ^ arr1 `letPair` \(arr1,res) -> res >! \_ ->
                     force st2 ^ arr2 `letPair` \(arr2,res) -> res >! \_ ->
                     join arr1 arr2 ⊗ put ()



foldArrayLeft :: HasArray exp
            => (a -> b -> b)
            -> b -> LinT exp (LState' (Array token a)) b
foldArrayLeft f b = do n <- sizeT
                       foldArrayT' n f b
  where
    foldArrayT' n f b | n <= 0    = return b
                      | otherwise = do b' <- foldArrayT' (n-1) f b
                                       a  <- readT (n-1)
                                       return $ f a b'

foldArrayRight :: HasArray exp
               => (a -> b -> b)
               -> b -> LinT exp (LState' (Array token a)) b
foldArrayRight f b = do n <- sizeT
                        foldArrayT' n f b
  where
    foldArrayT' n f b | n <= 0    = return b
                      | otherwise = do a <- readT (n-1)
                                       let b' = f a b
                                       foldArrayT' (n-1) f b'


toListT :: HasArray exp => LinT exp (LState' (Array token a)) [a]
toListT = foldArrayRight (:) []

fromListT :: HasArray exp => [α] -> LStateT exp (Array token α) ()
fromListT ls = fromListT' 0 ls
  where
    fromListT' _ []     = return ()
    fromListT' i (a:ls) = writeT i a >> fromListT' (i+1) ls
                             

allocT :: HasArray exp 
        => Int -> α -> (forall token. LStateT exp (Array token α) β)
        -> Lin exp β
allocT n a op = suspend $ alloc n a $ \arr ->
                          force op ^ arr `letPair` \(arr,b) ->
                          dealloc arr `letUnit` b
runArrayList  :: HasArray exp
              => (forall token. LStateT exp (Array token α) β) 
              -> [α] -> Lin exp ([α], β)
runArrayList op ls = allocT (length ls) (head ls) $ do fromListT ls
                                                       b <- op
                                                       ls' <- toListT
                                                       return (ls',b)

evalArrayList :: HasArray exp
              => (forall token. LStateT exp (Array token α) β) 
              -> [α] -> Lin exp [α]
evalArrayList op ls = do (ls,_) <- runArrayList op ls
                         return ls


test :: Lin Shallow [Int]
test = evalArrayList (return ()) [1,2,3]
