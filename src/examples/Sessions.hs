{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module Sessions where

import Data.Kind
import Data.Proxy
import Control.Concurrent hiding (Chan)
import Control.Concurrent.MVar

import Types
import Context hiding (End, In)
import Proofs
import Lang
import Classes
import Interface

data Session ty where
  SendSession :: ty -> Session ty -> Session ty
  RecvSession :: ty -> Session ty -> Session ty
  SendEnd :: Session ty 
  RecvEnd :: Session ty
type (:!:) = SendSession
type (:?:) = RecvSession
infixr 1 :!:
infixr 1 :?:
type family Dual (s :: Session ty) :: Session ty where
  Dual (SendSession t s) = t :?: Dual s
  Dual (RecvSession t s) = t :!: Dual s
  Dual SendEnd           = RecvEnd
  Dual RecvEnd           = SendEnd

data Channels (lang :: Lang sig) (s :: Session (LType sig)) where
  SendNil  :: C sig () -> Channels lang SendEnd
  RecvNil  :: C sig () -> Channels lang RecvEnd
  SendCons :: C sig (LVal lang t) 
           -> Channels lang s -> Channels lang (t :!: s)
  RecvCons :: C sig (LVal lang t) 
           -> Channels lang s -> Channels lang (t :?: s)

data SessionFrame (s :: Session ty) where
  SendFrame :: SessionFrame s -> SessionFrame (t :!: s)
  RecvFrame :: SessionFrame s -> SessionFrame (t :?: s)
  SendEndFrame :: SessionFrame SendEnd
  RecvEndFrame :: SessionFrame RecvEnd

class HasSessionEffect sig where
  type C sig (a :: *) = r | r -> a
  newC :: SigEffect sig (C sig a)
  recvC :: C sig a -> SigEffect sig a
  sendC :: C sig a -> a -> SigEffect sig ()
  forkEffect :: SigEffect sig () -> SigEffect sig ()

instance HasSessionEffect '(IO,tys) where
  type C '(IO,tys) a = MVar a
  newC = newEmptyMVar
  recvC = takeMVar
  sendC = putMVar
  forkEffect a = forkIO a >> return ()
  

newChannels :: forall sig (lang :: Lang sig) (s :: Session (LType sig)). 
               HasSessionEffect sig
            => SessionFrame s 
            -> SigEffect sig (Channels lang s, Channels lang (Dual s))
newChannels (SendFrame s) = do
    c0     <- newC @sig
    (c,c') <- newChannels @sig s
    return (SendCons @sig c0 c, RecvCons @sig c0 c')
newChannels (RecvFrame s) = do
    c0     <- newC
    (c,c') <- newChannels s
    return (RecvCons c0 c, SendCons c0 c')
newChannels SendEndFrame = do
    c0 <- newC
    return (SendNil c0, RecvNil c0)
newChannels RecvEndFrame = do
    c0 <- newC
    return (RecvNil c0, SendNil c0)


class KnownFrame (s :: Session ty) where
  frame :: SessionFrame s
instance KnownFrame SendEnd where
  frame = SendEndFrame
instance KnownFrame RecvEnd where
  frame = RecvEndFrame
instance KnownFrame s => KnownFrame (SendSession t s) where
  frame = SendFrame frame
instance KnownFrame s => KnownFrame (RecvSession t s) where
  frame = RecvFrame frame

class (Dual (Dual s) ~ s, KnownFrame s, KnownFrame (Dual s)) 
   => WFSession (s :: Session ty) 
instance WFSession SendEnd 
instance WFSession RecvEnd
instance WFSession s => WFSession (SendSession t s) 
instance WFSession s => WFSession (RecvSession t s) 

data SessionSig ty where
  ChannelSig :: Session ty -> SessionSig ty

type Chan s = ('Sig (InSig SessionSig sig) ('ChannelSig s) :: LType sig)

data SessionLExp :: forall sig. Lang sig -> Ctx sig -> LType sig -> * where
  Send    :: LExp lang g (t ⊗ Chan (t :!: s)) -> SessionLExp lang g (Chan s)
  Receive :: LExp lang g (Chan (t :?: s)) -> SessionLExp lang g (t ⊗ Chan s)
  Fork    :: SessionFrame s
          -> LExp lang g (Chan s ⊸ Chan SendEnd) 
          -> SessionLExp lang g (Chan (Dual s))
  Wait    :: LExp lang g (Chan RecvEnd) -> SessionLExp lang g One
  Link    :: LExp lang g (Chan s ⊗ Chan (Dual s)) -> SessionLExp lang g (Chan SendEnd)

data SessionLVal :: forall sig. Lang sig -> LType sig -> * where
  VChan   :: forall sig (lang :: Lang sig) s.
             Channels lang s -> SessionLVal lang (Chan s)

type SessionDom = '(SessionLExp, SessionLVal)

proxySession :: Proxy SessionDom
proxySession = Proxy

type HasSessions (lang :: Lang sig) =
    ( HasSessionEffect sig, Domain SessionDom lang
    , Domain OneDom lang, Domain TensorDom lang, Domain LolliDom lang
    , Domain PlusDom lang, Domain WithDom lang
    , Domain LowerDom lang )


send :: (HasSessions lang, CMerge g1 g2 g, WFSession s) 
     => LExp lang g1 t 
     -> LExp lang g2 (Chan (t :!: s)) 
     -> LExp lang g (Chan s)
send e e' = Dom proxySession $ Send (e ⊗ e')

receive :: (HasSessions lang, WFSession s) 
        => LExp lang g (Chan (t :?: s)) -> LExp lang g (t ⊗ Chan s)
receive = Dom proxySession . Receive

fork :: (HasSessions lang, WFSession s) 
     => LExp lang g ((Chan (Dual s)) ⊸ Chan SendEnd) -> LExp lang g (Chan s)
fork f = Dom proxySession $ Fork frame f

wait :: HasSessions lang => LExp lang g (Chan RecvEnd) -> LExp lang g One
wait = Dom proxySession . Wait

link :: (HasSessions lang,CMerge g1 g2 g, WFSession s)
     => LExp lang g1 (Chan s) -> LExp lang g2 (Chan (Dual s))
     -> LExp lang g (Chan SendEnd)
link e1 e2 = Dom proxySession $ Link (e1 ⊗ e2)


-- A common operation is to receive some classical data on a channel,
-- process it classically, and then send back the result.
processWith :: (HasSessions lang, WFSession s)
            => (a -> b)
            -> Lift lang (Chan (Lower a :?: Lower b :!: s) ⊸ Chan s)
processWith f = Suspend . λ $ \c ->
    receive (var c) `letPair` \(v,c) ->
    var v >! \a ->
    send (put $ f a) (var c)


instance HasSessions lang => Language SessionDom lang where
  evalDomain ρ (Send e)   = undefined
  evalDomain ρ (Fork s f) = do
      (c,c') <- newChannels s
      forkEffect $ do
         VChan (SendNil m) <- evalToValDom proxySession (ρ' $ VChan c) $ 
                                Dom proxyLolli $ App (pfM s g) f (var x)
         putMVar m ()
      return $ VDom proxySession $ VChan c'
    where
      g  = eCtxToSCtx ρ
      x  = knownFresh g
      ρ' v = eAddFresh ρ $ VDom proxySession v

      pfM :: forall s g. SessionFrame s -> SCtx g 
          -> Merge g (Singleton (Fresh g) (Chan s)) (Add (Fresh g) (Chan s) g)
      pfM _ = mergeFresh @g @(Chan s)
     
    

-- Examples

-- Examples from "A Semantics for Propositions as Sessions"
m :: (HasSessions lang, WFSession s) 
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

type ClientProto = Lower String :!: Lower Int :!: Lower String :?: RecvEnd
-- The server, an online seller, receives an item request and a credit card number,
-- and finally sends a receipt to the user. 
type ServerProto = Dual ClientProto

processOrder :: String -> Int -> String
processOrder item cc = "Processed order for " ++ item ++ "."

seller :: HasSessions lang
       => Lift lang (Chan ServerProto ⊸ Chan SendEnd)
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

type (:⊕:) (s1 :: Session (LType sig)) (s2 :: Session(LType sig))
  = Chan (Dual s1) ⊕ Chan (Dual s2) :!: SendEnd
type (:&:) s1 s2 
  = Chan s1 ⊕ Chan s2 :?: RecvEnd

selectL :: (HasSessions lang, WFSession s1, WFSession s2)
       => LExp lang 'Empty (Chan (s1 :⊕: s2) ⊸ Chan s1)
selectL = λ $ \c -> fork . λ $ \x ->
   send (inl $ var x) (var c)

selectR :: (HasSessions lang, WFSession s1, WFSession s2)
       => LExp lang 'Empty (Chan (s1 :⊕: s2) ⊸ Chan s2)
selectR = λ $ \c -> fork . λ $ \x ->
   send (inr $ var x) (var c)
-- selectR :: (HasSessions lang, WFSession s1, WFSession s2)
--         => LExp lang g (Chan (s1 `MakeChoice` s2))
--         -> LExp lang g (Chan s2)
-- selectR e = selectR' `app` e


offer :: (HasSessions lang, WFSession s1, WFSession s2)
      => LExp lang 'Empty (Chan (s1 :&: s2) 
      ⊸ (Chan s1 ⊸ t) & (Chan s2 ⊸ t)
      ⊸ t)
offer = λ $ \c -> λ $ \f ->
    receive (var c) `letPair` \(choice, c) ->
    wait (var c) `letUnit` 
    oplus `app` var f `app` var choice
  


-- Either sum two numbers or negate one of the numbers
exChoice :: (HasSessions lang, WFSession s)
         => Lift lang (Chan ((Lower (Int,Int) :?: Lower Int :!: s)
                         :&: (Lower Int :?: Lower Int :!: s))
                    ⊸ Chan s)
exChoice = Suspend . λ $ \c -> offer `app` var c `app`
           ( force (processWith (\(x,y) -> x+y))
           & force (processWith (\x -> -x))
           )
