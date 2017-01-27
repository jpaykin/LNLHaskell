{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module Sessions where

import Data.Kind
import Data.Proxy

import Types
import Context hiding (End, In)
import Proofs
import Lang
import Classes
import Interface

data Session ty where
  SendSession :: ty -> Session ty -> Session ty
  RecvSession :: ty -> Session ty -> Session ty
  SendEnd     :: Session ty 
  RecvEnd     :: Session ty
type (:!:) = SendSession
type (:?:) = RecvSession
infixr 1 :!:
infixr 1 :?:
type family Dual (s :: Session ty) :: Session ty where
  Dual (SendSession t s) = t :?: Dual s
  Dual (RecvSession t s) = t :!: Dual s
  Dual SendEnd           = RecvEnd
  Dual RecvEnd           = SendEnd

class (Dual (Dual s) ~ s) => WFSession (s :: Session ty) 
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
  Fork    :: LExp lang g (Chan s ⊸ Chan SendEnd) -> SessionLExp lang g (Chan (Dual s))
  Wait    :: LExp lang g (Chan RecvEnd) -> SessionLExp lang g One
  Link    :: LExp lang g (Chan s ⊗ Chan (Dual s)) -> SessionLExp lang g (Chan SendEnd)

data SessionLVal :: forall sig. Lang sig -> LType sig -> *

type SessionDom = '(SessionLExp, SessionLVal)

proxySession :: Proxy SessionDom
proxySession = Proxy

class (Domain OneDom lang, Domain TensorDom lang, Domain LolliDom lang,
       Domain LowerDom lang, Domain SessionDom lang, Domain PlusDom lang, Domain WithDom lang)
    => HasSessions lang
instance (Domain OneDom lang, Domain TensorDom lang, Domain LolliDom lang,
       Domain LowerDom lang, Domain SessionDom lang, Domain PlusDom lang, Domain WithDom lang)
    => HasSessions lang


send :: (HasSessions lang, CMerge g1 g2 g, WFSession s) 
     => LExp lang g1 t 
     -> LExp lang g2 (Chan (t :!: s)) 
     -> LExp lang g (Chan s)
send e e' = Dom proxySession $ Send (e ⊗ e')

receive :: (HasSessions lang, WFSession s) 
        => LExp lang g (Chan (t :?: s)) -> LExp lang g (t ⊗ Chan s)
receive = Dom proxySession . Receive

fork :: (HasSessions lang, WFSession s) 
     => LExp lang g (Chan (Dual s) ⊸ Chan SendEnd) -> LExp lang g (Chan s)
fork = Dom proxySession . Fork

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
  substDomain = undefined
  valToExpDomain = undefined
  evalDomain = undefined

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
