{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies,
             MagicHash
#-}

module Sessions where

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


type HasSessions exp = (HasOne exp, HasTensor exp, HasLolli exp, HasLower exp)

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


