{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, TemplateHaskell
#-}


module TH where

import Types
import Context
import Classes
import Lang
import Interface

import Prelude hiding (abs)
import Language.Haskell.TH
import qualified Data.Map.Lazy as M
import qualified Control.Monad.State as S
import Data.Maybe

--suspend :: Q Exp -> 
-- suspend x = $( x >>= transform >>= runQ )

natToS :: Nat -> NatSS
natToS Z = NatSS ZS
natToS (S n) = 
  case natToS n of NatSS n -> NatSS $ SS n


data QState a = QState (S.StateT (M.Map Name Nat) Q a)

instance Functor QState where
  fmap f (QState st) = QState $ S.fmap f st
instance Applicative QState where
  pure a = QState $ return a
  QState f <*> QState st = QState $ f <*> st
instance Monad QState where
  QState e >>= f = QState $ do
    a <- e
    case f a of QState e' -> e'
instance S.MonadState (M.Map Name Nat) QState where
--  state = QState . S.state
  get = QState S.get
  put a = QState $ S.put a

runQState :: Q a -> QState a
runQState q = QState (S.StateT $ \m -> q >>= \a -> return (a,m))

runStateQ :: QState a -> M.Map Name Nat -> Q a
runStateQ (QState st) m = S.evalStateT st m

--varNat :: NatSS -> LExp (Sing _ s) s
--varNat (NatSS n) = varNatS n

-- freshNat min ls returns the smallest nat >= min that is not in ls
freshNat :: Nat -> [Nat] -> Nat
freshNat min [] = min
freshNat min (min' : ls) = if min < min' then min
                           else freshNat min' ls

fresh :: QState Nat
fresh = do
  m  <- S.get
  ns <- return $ M.elems m
  return $ freshNat Z ns

transformPat :: Pat -> QState Pattern
transformPat (VarP n) = do
  x <- fresh
  m <- S.get
  S.put $ M.insert n x m
  return (PVar x)
transformPat _ = error "Other pattern"

transformPats :: [Pat] -> QState [Pattern]
transformPats [] = return []
transformPats (p : ps) = do
  p'  <- transformPat p 
  ps' <- transformPats ps
  return $ p':ps'

transform :: Exp -> QState (Maybe Exp)
transform (VarE n)          = do
  m <- S.get
  case M.lookup n m of
    Just x  -> do -- [| e |] >>= \e -> return (e,m)
      vName <- return $ mkName "Var"
      pf    <- case natToS x of NatSS x' -> runQState [| singS x' |]
      return . Just $ AppE (ConE vName) pf
    Nothing -> return . Just $ VarE n
transform (LamE pats e)     = do
  [ PVar x]    <- transformPats pats
  e'    <- transform e
  case (e',natToS x) of 
    (Just e',NatSS x') -> do
      ex <- runQState [|x'|]
      return . Just $ AppE (AppE (VarE $ mkName "abs") ex) e'

transform (ConE n)          = undefined
transform (LitE l)          = undefined
transform (AppE e1 e2)      = undefined
transform (InfixE e1 e e2)  = undefined
transform (UInfixE e1 e e2) = undefined
transform (ParensE e)       = undefined
transform (LamCaseE matches)= undefined
transform (TupE es)         = undefined         
transform (UnboxedTupE es)  = undefined
transform (CondE e1 e2 e3)  = undefined        
transform (MultiIfE ls)     = undefined
transform (LetE decls e)    = undefined  
transform (CaseE e matches) = undefined
transform (DoE stmts)       = undefined        
transform (CompE stmts)     = undefined
transform (ArithSeqE rng)   = undefined
transform (ListE es)        = undefined             
transform (SigE e t)        = undefined               
transform (RecConE n fs)    = undefined
transform (RecUpdE e fs)    = undefined
transform (StaticE e)       = undefined      
transform (UnboundVarE n)   = undefined

suspendTH :: Exp -> Exp
suspendTH e = AppE (VarE $ mkName "suspend") e

transformTH :: Q Exp -> Q Exp
transformTH m = do
  e <- m 
  me <- runStateQ (transform e) M.empty
  return $ suspendTH $ fromMaybe e me
  
