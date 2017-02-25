{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies,
             MagicHash, RecursiveDo
#-}

module Main where

import Control.Concurrent
import GHC.Prim

import Prelude hiding ((^))
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

main = run simpl >>= print


-- May need a separate fork

type family Dual (σ :: LType) = (r :: LType) | r -> σ where
    Dual One = Bottom
    Dual Bottom = One
    Dual (σ ⊗ τ)  = σ ⊸ Dual τ
    Dual (σ ⊸ τ) = σ ⊗ Dual τ
--    Dual (Lower α) = Lower α ⊸ Bot

-- Untyped channels
data UChan (σ :: LType) = UChan (Chan Any, Chan Any)


newU :: forall σ. IO (UChan σ,UChan (Dual σ))
newU = do 
    c1 <- newChan
    c2 <- newChan
    return $ (UChan (c1,c2), UChan (c2,c1))

sendU :: (Chan Any, Chan Any) -> a -> IO ()
sendU (cin,cout) a = writeChan cout $ unsafeCoerce# a

recvU :: (Chan Any, Chan Any) -> IO a
recvU (cin,cout) = unsafeCoerce# <$> readChan cin

-- if you have a UChan σ, σ is YOUR protocol
-- so if you have a UChan (σ ⊗ τ), you must send a $σ$ and then continue as $τ$
sendTensor :: UChan (σ ⊗ τ) -> LVal sig σ -> IO (UChan τ)
sendTensor (UChan c) v = sendU c v >> return (UChan c)

recvLolli :: UChan (σ ⊸ τ) -> IO (LVal sig σ, UChan τ)
recvLolli (UChan c) = do v <- recvU c
                         return (v,UChan c)

sendLower :: UChan (Lower α) -> α -> IO ()
sendLower (UChan c) a = sendU c a

recvLower :: UChan (Dual (Lower α)) -> IO α
recvLower (UChan c) = recvU c

sendOne :: UChan One -> IO ()
sendOne (UChan c) = sendU c ()

recvBot :: UChan Bottom -> IO ()
recvBot (UChan c) = recvU c



--forwardU :: UChan -> UChan -> IO ()
--forwardU c1 c2 = do
--    forkIO $ recvU c1 >>= sendU c2
--    forkIO $ recvU c2 >>= sendU c1
--    return ()

--yank :: UChan σ -> UChan (Dual σ)
--yank (cin,cout) = (cout,cin)

--class WFSession τ where
forward :: UChan τ -> UChan (Dual τ) -> IO ()
forward (UChan c1) (UChan c2) = forward' c1 c2
  where
    forward' c1 c2 = do
        forkIO $ recvU c1 >>= sendU c2 >> forward' c1 c2
        forkIO $ recvU c2 >>= sendU c1 >> forward' c1 c2
        return ()

-- Shallow Embedding ----------------------------------------

data Sessions
-- The UChan is the output channel
data instance LExp Sessions γ τ = SExp {runSExp :: SCtx Sessions γ -> UChan τ -> IO ()}
data instance LVal Sessions τ where
  Chan  :: UChan (Dual τ) -> LVal Sessions τ
type instance Effect Sessions = IO

instance Eval Sessions where
    eval e γ = do
        (cin,cout) <- newU
        runSExp e γ cin
        return $ Chan cout
    fromVPut (Chan c) = recvLower c

instance HasVar (LExp Sessions) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp Sessions γ σ
  var = SExp $ \γ (c :: UChan σ) -> 
            case singletonInv γ of Chan c' -> forward c c'


instance HasLolli (LExp Sessions) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp Sessions γ'' σ -> LExp Sessions γ' τ) -> LExp Sessions γ (σ ⊸ τ)  
  λ f = SExp $ \ρ (c :: UChan (σ ⊸ τ)) -> do
            (v,c) <- recvLolli c
            runSExp (f var) (add @x v ρ) c

  (^) :: forall γ1 γ2 γ σ τ. CMerge γ1 γ2 γ
      => LExp Sessions γ1 (σ ⊸ τ) -> LExp Sessions γ2 σ -> LExp Sessions γ τ
  e1 ^ e2 = SExp $ \ρ (c :: UChan τ) -> do 
            let (ρ1,ρ2) = split ρ
            (x,x') <- newU @σ -- x :: UChan σ, x' :: UChan σ⊥
            (y,y') <- newU @(σ ⊸ τ) -- y :: UChan (σ ⊸ τ), y' :: UChan (σ ⊗ Dual τ)
            forkIO $ runSExp e2 ρ2 x -- e2 :: σ
            forkIO $ runSExp e1 ρ1 y -- e1 :: σ ⊸ τ'⊥
            z      <- sendTensor y' (Chan x') 
            forward c z

instance HasTensor (LExp Sessions) where
    -- e1 ⊗ e2 = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
    --                             (x1,x2) <- newU
    --                             forkIO $ runSExp e1 ρ1 x1
    --                             sendU c (Chan x2)
    --                             runSExp e2 ρ2 c

    -- letPair :: forall x1 x2 σ1 σ2 τ γ1 γ2 γ2' γ γ2'' γ21 γ22.
    --          ( CMerge γ1 γ2 γ
    --          , CAddCtx x1 σ1 γ2 γ2'
    --          , CAddCtx x2 σ2 γ2' γ2''
    --          , CSingletonCtx x1 σ1 γ21
    --          , CSingletonCtx x2 σ2 γ22
    --          , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
    --   => LExp Sessions γ1 (σ1 ⊗ σ2)
    --   -> ((LExp Sessions γ21 σ1, LExp Sessions γ22 σ2) -> LExp Sessions γ2'' τ)
    --   -> LExp Sessions γ τ
    -- letPair e e' = SExp $ \ρ c ->  do 
    --                      let (ρ1,ρ2) = split ρ
    --                      (x1,x2) <- newU
    --                      forkIO $ runSExp e ρ1 x1
    --                      Chan y <- recvU x2
    --                      runSExp (e' (var,var)) (add @x2 (Chan x2) (add @x1 (Chan y) 
--                                                                        ρ2)) c
    
instance HasOne (LExp Sessions) where
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
  -- put a  = SExp $ \_ c -> sendU c (Just a)

  -- e >! f = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
  --                            (c1,c2) <- newU
  --                            forkIO $ runSExp e ρ1 c1
  --                            Chan x <- recvU c2
  --                            Just a <- recvU x
  --                            runSExp (f a) ρ2 c
