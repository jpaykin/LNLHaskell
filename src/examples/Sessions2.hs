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

import Prelude hiding ((^))
import Types
import Classes
import Tagless



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
          , x1 ~ Fresh γ, x2 ~ Fresh2 γ)
      => exp γ1 (σ1 ⊗ σ2)
      -> ((exp γ21 σ1, exp γ22 σ2) -> exp γ2'' τ)
      -> exp γ τ
recvOn = letPair

wait :: (HasOne exp, CMerge γ1 γ2 γ)
     => exp γ1 One -> exp γ2 τ -> exp γ τ
wait = letUnit

done :: HasOne exp => exp Empty One
done = unit


class (HasOne exp, HasTensor exp, HasLolli exp, HasLower exp)
   => HasSessions exp where
--  fork :: (CMerge γ1 γ2 γ, CSingletonCtx x σ γ2'', CAddCtx x σ γ2 γ2', x ~ Fresh γ2)
--       => exp γ1 σ -> (exp γ2'' σ -> exp γ2' τ) -> exp γ τ
    fork :: CMerge γ1 γ2 γ
         => exp γ1 σ -> exp γ2 (σ ⊸ τ) -> exp γ τ

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

serverBody :: HasSessions exp => Lift exp ServerProto
serverBody = Suspend . recv $ \x -> x >! \item ->
                       recv $ \y -> y >! \cc   ->
                       send (put $ processOrder item cc) done

clientBody :: HasSessions exp => Lift exp (ServerProto ⊸ Lower String)
clientBody = Suspend . λ $ \c ->
   sendOn (put "Tea") c $ \c ->
   sendOn (put 1234)  c $ \c ->
   recvOn c $ \(receipt,c) ->
   wait c receipt

--transaction :: HasSessions exp => Lift exp (Lower String)
--transaction = Suspend $ fork serverBody clientBody


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
forwardU (cin1,cout1) (cin2,cout2) = do
    forkIO $ readChan cout1 >>= writeChan cin2
    readChan cout2 >>= writeChan cin1

type Sessions = 'Sig IO SessionExp
data SessionExp sig (γ :: Ctx) (τ :: LType) where
  SessionExp :: (SCtx Sessions γ -> IO (LVal Sessions τ)) -> SessionExp sig γ τ

data SessionVal τ where
  Chan :: UChan -> SessionVal τ
  Bang :: a -> SessionVal (Lower a)
  VAbs :: (LVal Sessions σ -> IO (LVal Sessions τ)) -> SessionVal (σ ⊸ τ)
data instance LVal Sessions τ = SVal (SessionVal τ)
type family FromLower τ where
  FromLower (MkLType ('LowerSig a)) = a

instance HasVar (SessionExp sig) where
  var :: forall x σ γ. CSingletonCtx x σ γ => SessionExp sig γ σ
  var = SessionExp $ \g -> return $ singletonInv g


instance HasLolli (SessionExp sig) where
  λ :: forall x σ γ γ' γ'' τ. 
       (CAddCtx x σ γ γ', CSingletonCtx x σ γ'', x ~ Fresh γ)
    => (SessionExp sig γ'' σ -> SessionExp sig γ' τ) -> SessionExp sig γ (σ ⊸ τ)  
--  λ f = SessionExp $ \ρ -> do rec SVal (Chan c) <- g (add @x a ρ)
--                                  a             <- recvU c
--                              return . SVal $ Chan c
  λ f = SessionExp $ \ρ -> do
      (c1,c2) <- newU
      forkIO $ recvU c1 >>= \a -> g (add @x a ρ) >>= sendU c1
      return . SVal $ Chan c2
    where
      SessionExp g = f var

  SessionExp e1 ^ SessionExp e2 = SessionExp $ \ρ -> do
    (ρ1,ρ2) <- return $ split ρ
    SVal (Chan c)  <- e1 ρ1
    v2      <- e2 ρ2
    sendU c v2
    return . SVal $ Chan c

instance HasTensor (SessionExp sig) where
  SessionExp e1 ⊗ SessionExp e2 = SessionExp $ \ρ -> do
    (ρ1,ρ2) <- return $ split ρ
    v1      <- e1 ρ1
    SVal (Chan c)  <- e2 ρ2
    sendU c v1
    return . SVal $ Chan c
    
instance HasOne (SessionExp sig) where
instance HasLower (SessionExp sig) where

instance HasSessions (SessionExp sig) where
  fork (SessionExp e1) (SessionExp e2) = SessionExp $ \ρ -> do
    (ρ1,ρ2)       <- return $ split ρ
    v1            <- e1 ρ1
    SVal (VAbs f) <- e2 ρ2
    f v1
