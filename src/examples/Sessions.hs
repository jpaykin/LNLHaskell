{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies,
             MagicHash, RecursiveDo
#-}

module Sessions where

import Control.Concurrent
import GHC.Prim
import Control.Monad
import System.TimeIt

import Prelude hiding ((^))
import qualified Prelude as Prelude
import Types
import Classes
import Interface
import DeepEmbedding (Dom, Domain(..), VarName(..), LolliExp(..), OneExp(..))




send :: (HasTensor exp, CMerge γ1 γ2 γ)
     => exp γ1 σ1 -> exp γ2 σ2 -> exp γ (σ1 ⊗ σ2)
send = (⊗)

recv :: (HasLolli exp, CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
     => (exp γ'' σ -> exp γ' τ) -> exp γ (σ ⊸ τ)
recv = λ

sendOn :: (HasLolli exp, CMerge γ2 γ1 γ0, CMerge γ3 γ0 γ
          , CSingletonCtx x τ γ3'', CAddCtx x τ γ3 γ3', x ~ Fresh γ3)
       => exp γ1 σ -> exp γ2 (σ ⊸ τ) -> (exp γ3'' τ -> exp γ3' ρ) -> exp γ ρ
sendOn v c cont = (c ^ v) `letin` cont

recvOn :: (HasTensor exp
          , CMerge γ1 γ2 γ
          , CAddCtx x1 σ1 γ2 γ2'
          , CAddCtx x2 σ2 γ2' γ2''
          , CSingletonCtx x1 σ1 γ21
          , CSingletonCtx x2 σ2 γ22
          , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => exp γ1 (σ1 ⊗ σ2)
      -> ((exp γ21 σ1, exp γ22 σ2) -> exp γ2'' τ)
      -> exp γ τ
recvOn = letPair

wait :: (HasOne exp, CMerge γ1 γ2 γ)
     => exp γ1 One -> exp γ2 τ -> exp γ τ
wait = letUnit

done :: HasOne exp => exp Empty One
done = unit

type HasSessions exp = (HasOne exp, HasTensor exp, HasLolli exp, HasLower exp)

type ServerProto = Lower String ⊸ Lower Int ⊸ Lower String ⊗ One


processOrder :: String -> Int -> String
processOrder item cc = "Processed order for " ++ item ++ "."

serverBody :: HasSessions (LExp sig) => Lift sig ServerProto
serverBody = Suspend . recv $ \x -> x >! \item ->
                       recv $ \y -> y >! \cc   ->
                       send (put $ processOrder item cc) done

clientBody :: HasSessions (LExp sig) => Lift sig (ServerProto ⊸ Lower String)
clientBody = Suspend . λ $ \c ->
   sendOn (put "Tea") c $ \c ->
   sendOn (put 1234)  c $ \c ->
   recvOn c $ \(receipt,c) ->
   wait c receipt

connect :: HasLolli (LExp sig) => Lift sig proto -> Lift sig (proto ⊸ Lower α)  -> Lin sig α
connect server client = suspend $ force client ^ force server

transaction :: Lin Sessions String
transaction = connect serverBody clientBody


simpl :: Lin Sessions String
--simpl = suspend $ (λbang $ \s -> put $ "hello " ++ s) ^ put "world" where
simpl = connect server client where
    server :: Lift Sessions (Lower String)
    server = suspend $  put "world"
    client :: Lift Sessions (Lower String ⊸ Lower String)
    client = suspend $ recv $ \c ->
                       c >! \s ->
                       put $ "Hello " ++ s

--main = run simpl >>= print


-- May need a separate fork

type family Dual (σ :: LType) = (r :: LType) | r -> σ where
    Dual One = Bottom
    Dual Bottom = One
    Dual (σ ⊗ τ)  = σ ⊸ Dual τ
    Dual (σ ⊸ τ) = σ ⊗ Dual τ
--    Dual (Lower α) = Lower α ⊸ Bot

-- Untyped channels
data UChan = UChan (Chan Any, Chan Any)


newU :: forall σ. IO (UChan,UChan) -- UChan σ, UChan (Dual σ)
newU = do 
    c1 <- newChan
    c2 <- newChan
    return $ (UChan (c1,c2), UChan (c2,c1))

sendU :: UChan -> a -> IO ()
sendU (UChan (cin,cout)) a = writeChan cout $ unsafeCoerce# a

recvU :: UChan -> IO a
recvU (UChan (cin,cout)) = unsafeCoerce# <$> readChan cin

-- if you have a UChan σ, σ is YOUR protocol
-- so if you have a UChan (σ ⊗ τ), you must send a $σ$ and then continue as $τ$
--sendTensor :: UChan (σ ⊗ τ) -> LVal sig σ -> IO (UChan τ)
sendTensor :: UChan -> LVal sig σ -> IO UChan
sendTensor c v = sendU c v >> return c

--recvLolli :: UChan (σ ⊸ τ) -> IO (LVal sig σ, UChan τ)
recvLolli :: UChan -> IO (LVal sig σ, UChan)
recvLolli c = do v <- recvU c
                 return (v,c)

--sendLower :: UChan (Lower α) -> α -> IO ()
sendLower :: UChan -> α -> IO ()
sendLower c a = sendU c a

--recvLower :: UChan (Dual (Lower α)) -> IO α
recvLower :: UChan -> IO α
recvLower c = recvU c

--sendOne :: UChan One -> IO ()
sendOne :: UChan -> IO ()
sendOne c = sendU c ()

--recvBot :: UChan Bottom -> IO ()
recvBot :: UChan -> IO ()
recvBot c = recvU c



--forwardU :: UChan -> UChan -> IO ()
--forwardU c1 c2 = do
--    forkIO $ recvU c1 >>= sendU c2
--    forkIO $ recvU c2 >>= sendU c1
--    return ()

--yank :: UChan σ -> UChan (Dual σ)
--yank (cin,cout) = (cout,cin)

--class WFSession τ where
forward :: UChan -> UChan -> IO ()
forward c1 c2 = recvU c1 >>= sendU c2 >> forward c1 c2

--linkU :: UChan τ -> UChan (Dual τ) -> IO ()
linkU :: UChan -> UChan -> IO ()
linkU c1 c2 = do
    forkIO $ forward c1 c2
    forward c2 c1


-- Shallow Embedding ----------------------------------------

data Sessions
-- The UChan is the output channel
--data instance LExp Sessions γ τ = SExp {runSExp :: SCtx Sessions γ -> UChan τ -> IO ()}
data instance LExp Sessions γ τ = SExp {runSExp :: ECtx Sessions γ -> UChan -> IO ()}
data instance LVal Sessions τ where
--  Chan  :: UChan (Dual τ) -> LVal Sessions τ
    Chan :: UChan -> LVal Sessions τ
type instance Effect Sessions = IO

instance Eval Sessions where
    eval e γ = do
        (cin,cout) <- newU
        forkIO $ runSExp e γ cin
        return $ Chan cout
    fromVPut (Chan c) = recvLower c

instance HasVar (LExp Sessions) where
  var :: forall x σ γ. CSingletonCtx x σ γ => Sing x -> LExp Sessions γ σ
  var x = SExp $ \γ (c :: UChan) -> 
            case eLookup x γ of Chan c' -> linkU c c'


instance HasLolli (LExp Sessions) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp Sessions γ'' σ -> LExp Sessions γ' τ) -> LExp Sessions γ (σ ⊸ τ)  
  λ f = SExp $ \ρ (c :: UChan) -> do
            (v,c) <- recvLolli c
            runSExp (f $ var x) (add x v ρ) c
    where
      x = fresh @γ

  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp Sessions γ1 (σ ⊸ τ) -> LExp Sessions γ2 σ -> LExp Sessions γ τ
  e1 ^ e2 = SExp $ \ρ (c :: UChan) -> do 
            let (ρ1,ρ2) = split ρ
            (x,x') <- newU @σ -- x :: UChan σ, x' :: UChan σ⊥
            (y,y') <- newU @(σ ⊸ τ) -- y :: UChan (σ ⊸ τ), y' :: UChan (σ ⊗ Dual τ)
            forkIO $ runSExp e2 ρ2 x -- e2 :: σ
            forkIO $ runSExp e1 ρ1 y -- e1 :: σ ⊸ τ'⊥
            z      <- sendTensor y' (Chan x') 
            linkU c z

instance HasTensor (LExp Sessions) where
    e1 ⊗ e2 = SExp $ \ρ (c :: UChan) -> do
            let (ρ1,ρ2) = split ρ
            (x,x') <- newU -- @σ1
            forkIO $ runSExp e1 ρ1 x
            c' <- sendTensor c (Chan x')
            runSExp e2 ρ2 c'

    -- e1 ⊗ e2 = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
    --                             (x1,x2) <- newU
    --                             forkIO $ runSExp e1 ρ1 x1
    --                             sendU c (Chan x2)
    --                             runSExp e2 ρ2 c

    letPair :: forall x1 x2 σ1 σ2 τ γ1 γ2 γ2' γ γ2'' γ21 γ22.
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => LExp Sessions γ1 (σ1 ⊗ σ2)
      -> ((LExp Sessions γ21 σ1, LExp Sessions γ22 σ2) -> LExp Sessions γ2'' τ)
      -> LExp Sessions γ τ
    letPair e f = SExp $ \ρ (c :: UChan) -> do
                let (ρ1,ρ2) = split ρ
                (x,x') <- newU @(σ1 ⊗ σ2) -- x' :: Chan (σ1 ⊸ Dual σ2)
                forkIO $ runSExp e ρ1 x
                (v,y) <- recvLolli x' -- v :: LVal σ1, y :: UChan (Dual σ2)
                let ρ2' = add x2 (Chan y) (add x1 v ρ2)
                runSExp (f (var x1,var x2)) ρ2' c
      where 
        x1 = fresh @γ2
        x2 = fresh @γ2'

    -- letPair e e' = SExp $ \ρ c ->  do 
    --                      let (ρ1,ρ2) = split ρ
    --                      (x1,x2) <- newU
    --                      forkIO $ runSExp e ρ1 x1
    --                      Chan y <- recvU x2
    --                      runSExp (e' (var,var)) (add @x2 (Chan x2) (add @x1 (Chan y) 
--                                                                        ρ2)) c
    
instance HasOne (LExp Sessions) where
    unit = SExp $ \_ (c :: UChan) -> sendOne c

    letUnit e e' = SExp $ \ρ (c :: UChan) -> do
                let (ρ1,ρ2) = split ρ
                (x,x') <- newU @One
                forkIO $ runSExp e ρ1 x
                recvBot x' -- important, wait for result before continuing
                runSExp e' ρ2 c

--   -- unit = SExp $ \_ _ -> return ()
--   -- letUnit e e' = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
--   --                                  forkIO $ runSExp e ρ1 undefined
--   --                                  runSExp e' ρ2 c
--   unit = SExp $ \_ c -> sendU c ()
--   letUnit e e' = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
--                                    (x1,x2) <- newU
--                                    forkIO $ runSExp e ρ1 x1
--                                    Chan y <- recvU x2
--                                    () <- recvU y
--                                    runSExp e' ρ2 c

instance HasLower (LExp Sessions) where
    put a = SExp $ \_ (c :: UChan) -> sendLower c a

    (>!) :: forall γ1 γ2 γ α τ. CMerge γ1 γ2 γ
         => LExp Sessions γ1 (Lower α) -> (α -> LExp Sessions γ2 τ) 
         -> LExp Sessions γ τ
    e >! f = SExp $ \ρ (c :: UChan) -> do
                let (ρ1,ρ2) = split ρ
                (x,x') <- newU @(Lower α)
                forkIO $ runSExp e ρ1 x
                a <- recvLower x'
                runSExp (f a) ρ2 c

  -- put a  = SExp $ \_ c -> sendU c (Just a)

  -- e >! f = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
  --                            (c1,c2) <- newU
  --                            forkIO $ runSExp e ρ1 c1
  --                            Chan x <- recvU c2
  --                            Just a <- recvU x
  --                            runSExp (f a) ρ2 c

----------------
-- Comparison --
----------------

serverIO :: UChan -> IO ()
serverIO c = do item ← recvU c
                cc ← recvU c
                sendU c $ processOrder item cc
                sendU c ()

clientIO :: UChan -> IO String
clientIO c = do sendU c "Tea"
                sendU c 1234
                receipt ← recvU c
                () ← recvU c
                return receipt
              

transactionIO :: IO String
transactionIO = do (x,x') ← newU 
                   forkIO $ serverIO x
                   clientIO x'

transactions :: Int -> IO ()
transactions n = forM_ [0..n] (\_ -> run transaction)

transactionsIO :: Int -> IO ()
transactionsIO n = forM_ [0..n] (\_ -> transactionIO)

--transactions n = do
--    print $ "Executinr transaction " ++ show n ++ " times"
--    putStr "Linear:\t"
--    timeIt . void . run $ transaction

compareIO :: Int -> IO ()
compareIO n = do
    print $ "Executing transaction " ++ show n ++ " times"
    putStr "Linear:\t"
    timeIt $ transactions n
    putStr "Direct:\t"
    timeIt $ transactionsIO n

compareUpTo :: Int -> IO ()
compareUpTo n = forM_ ls compareIO 
  where
--    ls = [0..n]
    ls = ((Prelude.^) 2) <$> [0..n]
