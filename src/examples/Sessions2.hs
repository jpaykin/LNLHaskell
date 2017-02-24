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
--class (HasOne exp, HasTensor exp, HasLolli exp, HasLower exp)
--   => HasSessions exp where
--    fork :: CMerge γ1 γ2 γ
--         => exp γ1 σ -> exp γ2 (σ ⊸ τ) -> exp γ τ

type family Dual (σ :: LType) :: LType where
  Dual (MkLType ('TensorSig σ1 σ2)) = σ1 ⊸ Dual σ2
  Dual (MkLType ('LolliSig σ1 σ2))  = σ1 ⊗ Dual σ2
  Dual (MkLType 'OneSig)            = Bottom
  Dual (MkLType 'BottomSig)         = One
  Dual (MkLType ('PlusSig σ1 σ2))   = Dual σ1 & Dual σ2
  Dual (MkLType ('WithSig σ1 σ2))   = Dual σ1 ⊕ Dual σ2

type ServerProto = Lower String ⊸ Lower Int ⊸ Lower String ⊗ One
--type ClientProto = Dual ServerProto


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

transaction :: Lin SSessions String
transaction = connect serverBody clientBody


simpl :: Lin SSessions String
--simpl = suspend $ (λbang $ \s -> put $ "hello " ++ s) ^ put "world" where
simpl = connect server client where
    server :: Lift SSessions (Lower String)
    server = suspend $  put "world"
    client :: Lift SSessions (Lower String ⊸ Lower String)
    client = suspend $ recv $ \c ->
                       c >! \s ->
                       put $ "Hello " ++ s

main = run simpl >>= print


-- May need a separate fork

-- Untyped channels
type UChan = (Chan Any, Chan Any)
newU :: IO (UChan,UChan)
newU = do 
    c1 <- newChan
    c2 <- newChan
    return ((c1,c2),(c2,c1))
sendU :: UChan -> a -> IO ()
sendU (_,cout) a = writeChan cout $ unsafeCoerce# a
recvU :: UChan -> IO a
recvU (cin,_) = unsafeCoerce# <$> readChan cin

forwardU :: UChan -> UChan -> IO ()
forwardU c1 c2 = do
    forkIO $ recvU c1 >>= sendU c2
    forkIO $ recvU c2 >>= sendU c1
    return ()


-- Shallow Embedding ----------------------------------------

data SSessions
-- The UChan is the output channel
data instance LExp SSessions γ τ = SExp {runSExp :: SCtx SSessions γ -> UChan -> IO ()}
data instance LVal SSessions τ where
  Chan  :: UChan -> LVal SSessions τ
type instance Effect SSessions = IO

instance Eval SSessions where
    eval e γ = do
        (cin,cout) <- newU
        runSExp e γ cin
        return $ Chan cout
    fromVPut (Chan c) = recvU c

instance HasVar (LExp SSessions) where
  var :: forall x σ γ. CSingletonCtx x σ γ => LExp SSessions γ σ
  var = SExp $ \g c -> sendU c (singletonInv g)


instance HasLolli (LExp SSessions) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (LExp SSessions γ'' σ -> LExp SSessions γ' τ) -> LExp SSessions γ (σ ⊸ τ)  
  λ f = SExp $ \ρ c -> do
        Chan c' <- recvU c
        runSExp (f var) (add @x (Chan c') ρ) c

  e1 ^ e2 = SExp $ \ρ c -> do   let (ρ1,ρ2) = split ρ
--                                (x1,x2) <- newU
                                (y1,y2) <- newU
                                forkIO $ runSExp e1 ρ1 c
                                forkIO $ runSExp e2 ρ2 y1
                                sendU c (Chan y2)
--                                forwardU x2 c
                     

instance HasTensor (LExp SSessions) where
    e1 ⊗ e2 = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
                                (x1,x2) <- newU
                                forkIO $ runSExp e1 ρ1 x1
                                forkIO $ sendU c (Chan x2)
                                runSExp e2 ρ2 c -- continue as τ2

    letPair :: forall x1 x2 σ1 σ2 τ γ1 γ2 γ2' γ γ2'' γ21 γ22.
             ( CMerge γ1 γ2 γ
             , CAddCtx x1 σ1 γ2 γ2'
             , CAddCtx x2 σ2 γ2' γ2''
             , CSingletonCtx x1 σ1 γ21
             , CSingletonCtx x2 σ2 γ22
             , x1 ~ Fresh γ2, x2 ~ Fresh γ2')
      => LExp SSessions γ1 (σ1 ⊗ σ2)
      -> ((LExp SSessions γ21 σ1, LExp SSessions γ22 σ2) -> LExp SSessions γ2'' τ)
      -> LExp SSessions γ τ
    letPair e e' = SExp $ \ρ c ->  do 
                         let (ρ1,ρ2) = split ρ
                         (x1,x2) <- newU
                         forkIO $ runSExp e ρ1 x1
                         Chan y <- recvU x2
                         runSExp (e' (var,var)) (add @x2 (Chan x2) (add @x1 (Chan y) ρ2)) c
    
instance HasOne (LExp SSessions) where
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

instance HasLower (LExp SSessions) where
  put a  = SExp $ \_ c -> sendU c (Just a)

  e >! f = SExp $ \ρ c -> do let (ρ1,ρ2) = split ρ
                             (c1,c2) <- newU
                             forkIO $ runSExp e ρ1 c1
                             Chan x <- recvU c2
                             Just a <- recvU x
                             runSExp (f a) ρ2 c
