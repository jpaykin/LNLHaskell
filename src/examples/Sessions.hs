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
type family Dual (s :: Session sig) :: Session sig where
  Dual ('SendSession t s) = t :?: Dual s
  Dual ('RecvSession t s) = t :!: Dual s
  Dual 'SendEnd           = 'RecvEnd
  Dual 'RecvEnd           = 'SendEnd

data SSession (s :: Session sig) where
  SSendSession :: SSession s -> SSession (t :!: s)
  SRecvSession :: SSession s -> SSession (t :?: s)
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
 

newChannels :: forall sig (lang :: Lang sig) (s :: Session sig).
               HasSessions lang
            => SSession s
            -> SigEffect sig (LVal lang (Chan s), LVal lang (Chan (Dual s)))
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




linkChannels :: forall sig (lang :: Lang sig) (s :: Session sig).
                HasSessions lang
             => SessionLVal lang (Chan s)
             -> SessionLVal lang (Chan (Dual s))
             -> SigEffect sig ()
linkChannels (VSendEnd c)       (VRecvEnd c')        = recvC c >>= sendC c'
linkChannels (VRecvEnd c)       (VSendEnd c')        = recvC c' >>= sendC c
linkChannels (VSendSession c v) (VRecvSession c' v') = recvC c >>= sendC c' >>
    linkChannels (fromLVal proxySession v) (fromLVal proxySession v')
linkChannels (VRecvSession c v) (VSendSession c' v') = recvC c' >>= sendC c >>
    linkChannels (fromLVal proxySession v) (fromLVal proxySession v')
 

class KnownSession (s :: Session ty) where
  frame :: SSession s
instance KnownSession 'SendEnd where
  frame = SSendEnd
instance KnownSession 'RecvEnd where
  frame = SRecvEnd
instance KnownSession s => KnownSession ('SendSession t s) where
  frame = SSendSession frame
instance KnownSession s => KnownSession ('RecvSession t s) where
  frame = SRecvSession frame

class (Dual (Dual s) ~ s, KnownSession s, KnownSession (Dual s)) 
   => WFSession (s :: Session ty) 
instance WFSession 'SendEnd 
instance WFSession 'RecvEnd
instance WFSession s => WFSession ('SendSession t s) 
instance WFSession s => WFSession ('RecvSession t s) 


-- The data type
data SessionSig sig where
  ChannelSig :: Session sig -> SessionSig sig

type Chan s = ('LType (InSig SessionSig sig) ('ChannelSig s) :: LType sig)

data SessionLExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Send    :: LExp lang g (t ⊗ Chan (t :!: s)) -> SessionLExp lang g (Chan s)
  Receive :: LExp lang g (Chan (t :?: s)) -> SessionLExp lang g (t ⊗ Chan s)
  Fork    :: SSession s
          -> LExp lang g (Chan s ⊸ Chan 'SendEnd) 
          -> SessionLExp lang g (Chan (Dual s))
  Wait    :: LExp lang g (Chan 'RecvEnd) -> SessionLExp lang g One
  Link    :: LExp lang g (Chan s ⊗ Chan (Dual s)) 
          -> SessionLExp lang g (Chan 'SendEnd)

data SessionLVal :: forall sig. Lang sig -> LType sig -> * where
  VSendEnd :: forall sig (lang :: Lang sig). 
              C (SigEffect sig) () -> SessionLVal lang (Chan 'SendEnd)
  VRecvEnd :: forall sig (lang :: Lang sig). 
              C (SigEffect sig) () -> SessionLVal lang (Chan 'RecvEnd)
  VSendSession :: forall sig (lang :: Lang sig) (s :: Session sig) (t :: LType sig).
                  C (SigEffect sig) (LVal lang t) -> LVal lang (Chan s) 
               -> SessionLVal lang (Chan (t :!: s))
  VRecvSession :: forall sig (lang :: Lang sig) (s :: Session sig) (t :: LType sig).
                  C (SigEffect sig) (LVal lang t) -> LVal lang (Chan s) 
               -> SessionLVal lang (Chan (t :?: s))


type SessionDom = '(SessionLExp, SessionLVal)

proxySession :: Proxy SessionDom
proxySession = Proxy

instance Show (SessionLExp lang g t) where
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
     => LExp lang g1 t 
     -> LExp lang g2 (Chan (t :!: s)) 
     -> LExp lang g (Chan s)
send e e' = Dom proxySession $ Send (e ⊗ e')

vSendSession :: forall sig (lang :: Lang sig) t s. 
                HasSessions lang
             => C (SigEffect sig) (LVal lang t)
             -> LVal lang (Chan s)
             -> LVal lang (Chan (t :!: s))
vSendSession c v = VDom proxySession $ VSendSession c v

vRecvSession :: forall sig (lang :: Lang sig) t s. 
                HasSessions lang
             => C (SigEffect sig) (LVal lang t)
             -> LVal lang (Chan s)
             -> LVal lang (Chan (t :?: s))
vRecvSession c v = VDom proxySession $ VRecvSession c v

vSendEnd :: forall sig (lang :: Lang sig). HasSessions lang
         => C (SigEffect sig) () -> LVal lang (Chan 'SendEnd)
vSendEnd c = VDom proxySession $ VSendEnd c
vRecvEnd :: forall sig (lang :: Lang sig). HasSessions lang
         => C (SigEffect sig) () -> LVal lang (Chan 'RecvEnd)
vRecvEnd c = VDom proxySession $ VRecvEnd c


receive :: HasSessions lang
        => LExp lang g (Chan (t :?: s)) -> LExp lang g (t ⊗ Chan s)
receive = Dom proxySession . Receive

fork :: (HasSessions lang, WFSession s) 
     => LExp lang g ((Chan (Dual s)) ⊸ Chan 'SendEnd) -> LExp lang g (Chan s)
fork f = Dom proxySession $ Fork frame f

wait :: HasSessions lang => LExp lang g (Chan 'RecvEnd) -> LExp lang g One
wait = Dom proxySession . Wait

link :: (HasSessions lang,CMerge g1 g2 g)
     => LExp lang g1 (Chan s) -> LExp lang g2 (Chan (Dual s))
     -> LExp lang g (Chan 'SendEnd)
link e1 e2 = Dom proxySession $ Link (e1 ⊗ e2)


-- A common operation is to receive some classical data on a channel,
-- process it classically, and then send back the result.
processWith :: HasSessions lang
            => (a -> b)
            -> Lift lang (Chan (Lower a :?: Lower b :!: s) ⊸ Chan s)
processWith f = Suspend . λ $ \c ->
    receive (var c) `letPair` \(v,c) ->
    var v >! \a ->
    send (put $ f a) (var c)


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

    
evalApplyValue :: forall sig (lang :: Lang sig) g s t.
                  Domain LolliDom lang
               => ECtx lang g -> LExp lang g (s ⊸ t) -> LVal lang s 
               -> SigEffect sig (LVal lang t)
evalApplyValue ρ e v = eval' ρ' (Dom proxyLolli $ App pfM e (var x))
  where
    x :: SNat (Fresh g)
    x = knownFresh ρ

    ρ' :: ECtx lang (Add (Fresh g) s g)
    ρ' = addFreshSCtx ρ (ValData v)

    pfM :: Merge g (Singleton (Fresh g) s) (Add (Fresh g) s g)
    pfM = mergeAddFresh @s ρ
    

-- Examples

type MySessionSig = ('Sig IO '[ SessionSig, TensorSig, OneSig, LolliSig, PlusSig, WithSig, LowerSig ] :: Sig)
type MySessionDom = ('Lang '[ SessionDom, TensorDom, OneDom, LolliDom, PlusDom, WithDom, LowerDom ] :: Lang MySessionSig)

-- Examples from "A Semantics for Propositions as Sessions"
m :: HasSessions lang 
  => Lift lang (Chan (Lower (Int,Int) :?: Lower Int :!: s) ⊸ Chan s)
m = Suspend . λ $ \z ->
      receive (var z) `letPair` \(v,z) ->
      var v >! \(x,y) ->
      send (put (x+y)) $ var z

n :: HasSessions lang => Lift lang (Chan (Lower (Int,Int) :!: Lower Int :?: RecvEnd) ⊸ Lower Int)
n = Suspend . λ $ \z ->
      send (put (6,7)) (var z) `letin` \z ->
      receive (var z) `letPair` \(x,z) ->
      wait (var z) `letUnit`
      var x

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
    receive (var c) `letPair` \(x,c) -> var x >! \ item -> -- receive the item request
    receive (var c) `letPair` \(y,c) -> var y >! \ cc   -> -- receive the credit card number
    send (put $ processOrder item cc) (var c)

buyer :: HasSessions lang
      => Lift lang (Chan ClientProto ⊸ Lower String)
buyer = Suspend . λ $ \c ->
    send (put "Tea") (var c) `letin` \c ->
    send (put 5555) (var c) `letin` \c ->
    receive (var c) `letPair` \(receipt,c) ->
    wait (var c) `letUnit` 
    var receipt

transaction :: HasSessions lang 
            => Lin lang String
transaction = suspendL $ force buyer `app` fork (force seller)

-- Encoding choice

type (:⊕:) (s1 :: Session sig) (s2 :: Session sig)
  = Chan (Dual s1) ⊕ Chan (Dual s2) :!: 'SendEnd
type (:&:) s1 s2 
  = Chan s1 ⊕ Chan s2 :?: 'RecvEnd

selectL :: (HasSessions lang, WFSession s1)
       => LExp lang 'Empty (Chan (s1 :⊕: s2) ⊸ Chan s1)
selectL = λ $ \c -> fork . λ $ \x ->
   send (inl $ var x) (var c)

selectR :: (HasSessions lang, WFSession s2)
       => LExp lang 'Empty (Chan (s1 :⊕: s2) ⊸ Chan s2)
selectR = λ $ \c -> fork . λ $ \x ->
   send (inr $ var x) (var c)
-- selectR :: (HasSessions lang, WFSession s1, WFSession s2)
--         => LExp lang g (Chan (s1 `MakeChoice` s2))
--         -> LExp lang g (Chan s2)
-- selectR e = selectR' `app` e


offer :: HasSessions lang
      => LExp lang 'Empty (Chan (s1 :&: s2) 
      ⊸ (Chan s1 ⊸ t) & (Chan s2 ⊸ t)
      ⊸ t)
offer = λ $ \c -> λ $ \f ->
    receive (var c) `letPair` \(choice, c) ->
    wait (var c) `letUnit` 
    oplus `app` var f `app` var choice
  


-- Either sum two numbers or negate one of the numbers
exChoice :: HasSessions lang
         => Lift lang (Chan ((Lower (Int,Int) :?: Lower Int :!: s)
                         :&: (Lower Int :?: Lower Int :!: s))
                    ⊸ Chan s)
exChoice = Suspend . λ $ \c -> offer `app` var c `app`
           ( force (processWith (\(x,y) -> x+y))
           & force (processWith (\x -> -x))
           )
