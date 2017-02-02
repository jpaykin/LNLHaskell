{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}
-- {-# OPTIONS_GHC -Wall -Wcompat #-}

module Sessions where

import Data.Kind
import Data.Proxy
import Control.Concurrent hiding (Chan)
import Debug.Trace

import Prelim
import Types
import Context hiding (End, In)
import Proofs
import Lang
import Classes
import Interface

data Session sig where
  SendSession :: LType sig -> Session sig -> Session sig
  RecvSession :: LType sig -> Session sig -> Session sig
  SendEnd :: Session sig
  RecvEnd :: Session sig
type (:!:) = 'SendSession
type (:?:) = 'RecvSession
infixr 1 :!:
infixr 1 :?:
type family Dual (σ :: Session sig) :: Session sig where
  Dual ('SendSession τ σ) = τ :?: Dual σ
  Dual ('RecvSession τ σ) = τ :!: Dual σ
  Dual 'SendEnd           = 'RecvEnd
  Dual 'RecvEnd           = 'SendEnd

data SSession (σ :: Session sig) where
  SSendSession :: SSession σ -> SSession (τ :!: σ)
  SRecvSession :: SSession σ -> SSession (τ :?: σ)
  SSendEnd     :: SSession 'SendEnd
  SRecvEnd :: SSession 'RecvEnd

class Monad m => HasSessionEffect m where
  type C m a = r | r -> a
  newC :: m (C m a)
  recvC :: C m a -> m a
  sendC :: C m a -> a -> m ()
  forkEffect :: m () -> m ()

instance HasSessionEffect IO where
  type C IO a = MVar a
  newC = newEmptyMVar
  recvC = takeMVar
  sendC = putMVar
  forkEffect a = forkIO a >> return ()
 

newChannels :: forall sig (lang :: Lang sig) (σ :: Session sig).
               HasSessions lang
            => SSession σ
            -> SigEffect sig (LVal lang (Chan σ), LVal lang (Chan (Dual σ)))
newChannels (SSendSession s) = do
    c <- newC
    (v1,v2) <- newChannels s
    return $ (vSendSession c v1, vRecvSession c v2)
newChannels (SRecvSession s) = do
    c <- newC
    (v1,v2) <- newChannels s
    return $ (vRecvSession c v1, vSendSession c v2)
newChannels SSendEnd = do
    c <- newC
    return $ (vSendEnd c, vRecvEnd c)
newChannels SRecvEnd = do
    c <- newC
    return $ (vRecvEnd c, vSendEnd c)




linkChannels :: forall sig (lang :: Lang sig) (σ :: Session sig).
                HasSessions lang
             => SessionLVal lang (Chan σ)
             -> SessionLVal lang (Chan (Dual σ))
             -> SigEffect sig ()
linkChannels (VSendEnd c)       (VRecvEnd c')        = recvC c >>= sendC c'
linkChannels (VRecvEnd c)       (VSendEnd c')        = recvC c' >>= sendC c
linkChannels (VSendSession c v) (VRecvSession c' v') = recvC c >>= sendC c' >>
    linkChannels (fromLVal proxySession v) (fromLVal proxySession v')
linkChannels (VRecvSession c v) (VSendSession c' v') = recvC c' >>= sendC c >>
    linkChannels (fromLVal proxySession v) (fromLVal proxySession v')
 

class KnownSession (σ :: Session ty) where
  frame :: SSession σ
instance KnownSession 'SendEnd where
  frame = SSendEnd
instance KnownSession 'RecvEnd where
  frame = SRecvEnd
instance KnownSession σ => KnownSession ('SendSession τ σ) where
  frame = SSendSession frame
instance KnownSession σ => KnownSession ('RecvSession τ σ) where
  frame = SRecvSession frame

class (Dual (Dual σ) ~ σ, KnownSession σ, KnownSession (Dual σ)) 
   => WFSession (σ :: Session ty) 
instance WFSession 'SendEnd 
instance WFSession 'RecvEnd
instance WFSession σ => WFSession ('SendSession τ σ) 
instance WFSession σ => WFSession ('RecvSession τ σ) 


-- The data type
data SessionSig sig where
  ChannelSig :: Session sig -> SessionSig sig

type Chan σ = ('LType (InSig SessionSig sig) ('ChannelSig σ) :: LType sig)

data SessionLExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Send    :: LExp lang g (τ ⊗ Chan (τ :!: σ)) -> SessionLExp lang g (Chan σ)
  Receive :: LExp lang g (Chan (τ :?: σ)) -> SessionLExp lang g (τ ⊗ Chan σ)
  Fork    :: SSession σ
          -> LExp lang g (Chan σ ⊸ Chan 'SendEnd) 
          -> SessionLExp lang g (Chan (Dual σ))
  Wait    :: LExp lang g (Chan 'RecvEnd) -> SessionLExp lang g One
  Link    :: LExp lang g (Chan σ ⊗ Chan (Dual σ)) 
          -> SessionLExp lang g (Chan 'SendEnd)

data SessionLVal :: forall sig. Lang sig -> LType sig -> * where
  VSendEnd :: forall sig (lang :: Lang sig). 
              C (SigEffect sig) () -> SessionLVal lang (Chan 'SendEnd)
  VRecvEnd :: forall sig (lang :: Lang sig). 
              C (SigEffect sig) () -> SessionLVal lang (Chan 'RecvEnd)
  VSendSession :: forall sig (lang :: Lang sig) (σ :: Session sig) (τ :: LType sig).
                  C (SigEffect sig) (LVal lang τ) -> LVal lang (Chan σ) 
               -> SessionLVal lang (Chan (τ :!: σ))
  VRecvSession :: forall sig (lang :: Lang sig) (σ :: Session sig) (τ :: LType sig).
                  C (SigEffect sig) (LVal lang τ) -> LVal lang (Chan σ) 
               -> SessionLVal lang (Chan (τ :?: σ))


type SessionDom = '(SessionLExp, SessionLVal)

proxySession :: Proxy SessionDom
proxySession = Proxy

instance Show (SessionLExp lang g τ) where
  show (Send e) = "Send(" ++ show e ++ ")"
  show (Receive e) = "Receive(" ++ show e ++ ")"
  show (Fork _ f) = "Fork(" ++ show f ++ ")"
  show (Wait e) = "Wait(" ++ show e ++ ")"
  show (Link e) = "Link(" ++ show e ++ ")"

type HasSessions (lang :: Lang sig) =
    ( HasSessionEffect (SigEffect sig), WFDomain SessionDom lang
    , WFDomain OneDom lang, WFDomain TensorDom lang, WFDomain LolliDom lang
    , WFDomain PlusDom lang, WFDomain WithDom lang
    , WFDomain LowerDom lang )


send :: (HasSessions lang, CMerge g1 g2 g)
     => LExp lang g1 τ 
     -> LExp lang g2 (Chan (τ :!: σ)) 
     -> LExp lang g (Chan σ)
send e e' = Dom proxySession $ Send (e ⊗ e')

vSendSession :: forall sig (lang :: Lang sig) τ σ. 
                HasSessions lang
             => C (SigEffect sig) (LVal lang τ)
             -> LVal lang (Chan σ)
             -> LVal lang (Chan (τ :!: σ))
vSendSession c v = VDom proxySession $ VSendSession c v

vRecvSession :: forall sig (lang :: Lang sig) τ σ. 
                HasSessions lang
             => C (SigEffect sig) (LVal lang τ)
             -> LVal lang (Chan σ)
             -> LVal lang (Chan (τ :?: σ))
vRecvSession c v = VDom proxySession $ VRecvSession c v

vSendEnd :: forall sig (lang :: Lang sig). HasSessions lang
         => C (SigEffect sig) () -> LVal lang (Chan 'SendEnd)
vSendEnd c = VDom proxySession $ VSendEnd c
vRecvEnd :: forall sig (lang :: Lang sig). HasSessions lang
         => C (SigEffect sig) () -> LVal lang (Chan 'RecvEnd)
vRecvEnd c = VDom proxySession $ VRecvEnd c


receive :: HasSessions lang
        => LExp lang g (Chan (τ :?: σ)) -> LExp lang g (τ ⊗ Chan σ)
receive = Dom proxySession . Receive

fork :: (HasSessions lang, WFSession σ) 
     => LExp lang g ((Chan (Dual σ)) ⊸ Chan 'SendEnd) -> LExp lang g (Chan σ)
fork f = Dom proxySession $ Fork frame f

wait :: HasSessions lang => LExp lang g (Chan 'RecvEnd) -> LExp lang g One
wait = Dom proxySession . Wait

link :: (HasSessions lang,CMerge g1 g2 g)
     => LExp lang g1 (Chan σ) -> LExp lang g2 (Chan (Dual σ))
     -> LExp lang g (Chan 'SendEnd)
link e1 e2 = Dom proxySession $ Link (e1 ⊗ e2)


-- A common operation is to receive some classical data on a channel,
-- process it classically, and then send back the result.
processWith :: HasSessions lang
            => (a -> b)
            -> Lift lang (Chan (Lower a :?: Lower b :!: σ) ⊸ Chan σ)
processWith f = Suspend . λ $ \c ->
    receive c `letPair` \(v,c) ->
    v >! \a ->
    send (put $ f a) c


instance HasSessions lang => Domain SessionDom (lang  :: Lang sig) where
  evalDomain ρ (Send e)   = do
    VPair v1 v2        <- evalToValDom proxyTensor ρ e
    VSendSession c v2' <- return $ fromLVal proxySession v2
    sendC c v1
    return v2'
  evalDomain ρ (Receive e) = do
    VRecvSession c v <- evalToValDom proxySession ρ e
    v' <- recvC c
    return $ vpair v' v
  evalDomain ρ (Fork s f) = do
    (v,v') <- newChannels s
    forkEffect $ do
        VSendEnd c <- fromLVal proxySession <$> evalApplyValue ρ f v
        sendC c ()
    return v'
  evalDomain ρ (Wait e) = do
    VRecvEnd c <- evalToValDom proxySession ρ e
    () <- recvC c
    return vunit
  evalDomain ρ (Link e) = do
    VPair v1 v2 <- evalToValDom proxyTensor ρ e
    linkChannels (fromLVal proxySession v1) (fromLVal proxySession v2) 
    c <- newC
    return $ vSendEnd c

    
    

-- Examples

type MySessionSig = ('Sig IO '[ SessionSig, TensorSig, OneSig, LolliSig, PlusSig, WithSig, LowerSig ] :: Sig)
type MySessionDom = ('Lang '[ SessionDom, TensorDom, OneDom, LolliDom, PlusDom, WithDom, LowerDom ] :: Lang MySessionSig)

-- Examples from "A Semantics for Propositions as Sessions"
m :: HasSessions lang 
  => Lift lang (Chan (Lower (Int,Int) :?: Lower Int :!: σ) ⊸ Chan σ)
m = Suspend . λ $ \z ->
      receive z `letPair` \(v,z) ->
      v >! \(x,y) ->
      send (put (x+y)) z

n :: HasSessions lang => Lift lang (Chan (Lower (Int,Int) :!: Lower Int :?: RecvEnd) ⊸ Lower Int)
n = Suspend . λ $ \z ->
      send (put (6,7)) z `letin` \z ->
      receive z `letPair` \(x,z) ->
      wait z `letUnit` x

p :: HasSessions lang => Lin lang Int
p = suspendL $ force n `app` fork (force m) 

-- "Store" example from "Linear Logic Propositions as Session Types"

type ClientProto = Lower String :!: Lower Int :!: Lower String :?: 'RecvEnd
-- The server, an online seller, receives an item request and a credit card number,
-- and finally sends a receipt to the user. 
type ServerProto = Dual ClientProto

processOrder :: String -> Int -> String
processOrder item cc = "Processed order for " ++ item ++ "."

seller :: HasSessions lang
       => Lift lang (Chan ServerProto ⊸ Chan 'SendEnd)
seller = Suspend . λ $ \c ->
    receive c `letPair` \(x,c) -> x >! \ item -> -- receive the item request
    receive c `letPair` \(y,c) -> y >! \ cc   -> -- receive the credit card number
    send (put $ processOrder item cc) c

buyer :: HasSessions lang
      => Lift lang (Chan ClientProto ⊸ Lower String)
buyer = Suspend . λ $ \c ->
    send (put "Tea") c `letin` \c ->
    send (put 5555) c `letin` \c ->
    receive c `letPair` \(receipt,c) ->
    wait c `letUnit` 
    receipt

transaction :: HasSessions lang 
            => Lin lang String
transaction = suspendL $ force buyer `app` fork (force seller)

-- Encoding choice

type (:⊕:) (σ1 :: Session sig) (σ2 :: Session sig)
  = Chan (Dual σ1) ⊕ Chan (Dual σ2) :!: 'SendEnd
type (:&:) σ1 σ2 
  = Chan σ1 ⊕ Chan σ2 :?: 'RecvEnd

selectL :: (HasSessions lang, WFSession σ1)
       => LExp lang 'Empty (Chan (σ1 :⊕: σ2) ⊸ Chan σ1)
selectL = λ $ \c -> fork . λ $ \x ->
   send (inl x) c

selectR :: (HasSessions lang, WFSession σ2)
       => LExp lang 'Empty (Chan (σ1 :⊕: σ2) ⊸ Chan σ2)
selectR = λ $ \c -> fork . λ $ \x ->
   send (inr x) c
-- selectR :: (HasSessions lang, WFSession σ1, WFSession σ2)
--         => LExp lang g (Chan (σ1 `MakeChoice` σ2))
--         -> LExp lang g (Chan σ2)
-- selectR e = selectR' `app` e


offer :: HasSessions lang
      => LExp lang 'Empty (Chan (σ1 :&: σ2) 
      ⊸ (Chan σ1 ⊸ τ) & (Chan σ2 ⊸ τ)
      ⊸ τ)
offer = λ $ \c -> λ $ \f ->
    receive c `letPair` \(choice, c) ->
    wait c `letUnit` 
    oplus `app` f `app` choice
  


-- Either sum two numbers or negate one of the numbers
exChoice :: HasSessions lang
         => Lift lang (Chan ((Lower (Int,Int) :?: Lower Int :!: σ)
                         :&: (Lower Int :?: Lower Int :!: σ))
                    ⊸ Chan σ)
exChoice = Suspend . λ $ \c -> offer `app` c `app`
           ( force (processWith (\(x,y) -> x+y))
           & force (processWith (\x -> -x))
           )
