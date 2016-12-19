{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, LambdaCase,
             EmptyCase
#-}

module Domain where

import Data.Kind
import Data.Constraint
import Data.Proxy

import Types
import Context
import Proofs
import Lang 



data (:+:) (sig1 :: TypeSig) (sig2 :: TypeSig) :: TypeSig where
  AndTy1 :: LType '(m,sig1) -> (sig1 :+: sig2) (LType '(m,sig1 :+: sig2))
  AndTy2 :: LType '(m,sig2) -> (sig1 :+: sig2) (LType '(m,sig1 :+: sig2))
--type family (:+:) (sig1 :: Sig) (sig2 :: Sig) :: Sig where
--  '(m,ty1) :+: '(m,ty2) = '(m, AndTypeSig ty1 ty2)

data AndVal (val1 :: ValDom sig) (val2 :: ValDom sig) :: ValDom sig where
  AndVal1 :: val1 (LVal dom) t -> AndVal val1 val2 (LVal dom) t
  AndVal2 :: val2 (LVal dom) t -> AndVal val1 val2 (LVal dom) t
type AndDom (dom1 :: Dom sig) (dom2 :: Dom sig) = (AndVal dom1 dom2 :: Dom sig)

data AndExp (exp1 :: ExpDom sig) (exp2 :: ExpDom sig) :: ExpDom sig where
  AndExp1 :: exp1 (LExp dom) g t -> AndExp exp1 exp2 (LExp dom) g t
  AndExp2 :: exp2 (LExp dom) g t -> AndExp exp1 exp2 (LExp dom) g t


instance (Domain dom exp1, Domain dom exp2)
      => Domain dom (AndExp exp1 exp2) where

  substDomain _ pfA s (AndExp1 e) = substDomain Proxy pfA s e
  substDomain _ pfA s (AndExp2 e) = substDomain Proxy pfA s e

  evalDomain _ (AndExp1 e) = evalDomain Proxy e
  evalDomain _ (AndExp2 e) = evalDomain Proxy e

instance (ToExp dom1 exp, ToExp dom2 exp)
      => ToExp (AndDom dom1 dom2) exp where

  valToExpDomain p (AndVal1 v) = valToExpDomain p v
  valToExpDomain p (AndVal2 v) = valToExpDomain p v


instance ToExp dom exp1 => ToExp dom (AndExp exp1 exp2) where
  valToExpDomain p v = AndExp1 $ valToExpDomain (Proxy :: Proxy exp1) v
-- To do
--instance ToExp dom exp2 => ToExp dom (AndExp exp1 exp2) where
--  valToExpDomain p v = AndExp2 $ valToExpDomain (Proxy :: Proxy exp2) v
