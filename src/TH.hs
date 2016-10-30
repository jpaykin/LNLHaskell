{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables,
             EmptyCase, TemplateHaskell, QuasiQuotes
#-}


module TH where

import Types
import Context
import Classes
import Lang
import Interface

import Prelude hiding (abs)
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Data.Map.Lazy as M
import qualified Control.Monad.State as S
import Data.Maybe
import Control.Monad.Trans.Maybe

--suspend :: Q Exp -> 
-- suspend x = $( x >>= transform >>= runQ )

natToS :: Nat -> NatSS
natToS Z = NatSS ZS
natToS (S n) = 
  case natToS n of NatSS n -> NatSS $ SS n

data ELExp where
  ELExp :: forall t g. LExp g t -> ELExp

data MyState = MyState { mynames :: M.Map Name Ident
                       , myconst :: M.Map Name ELExp
                       }

data QState a = QState (MaybeT (S.StateT MyState Q) a)

instance Functor QState where
  fmap f (QState st) = QState $ S.fmap f st
instance Applicative QState where
  pure a = QState $ return a
  QState f <*> QState st = QState $ f <*> st
instance Monad QState where
  QState e >>= f = QState $ do
    a <- e
    case f a of QState e' -> e'
instance S.MonadState MyState QState where
  get = QState S.get
  put a = QState $ S.put a

getMap :: QState (M.Map Name Ident)
getMap = S.get >>= return . mynames

putMap :: M.Map Name Ident -> QState ()
putMap m = do 
  cs <- getConstants
  S.put $ MyState { mynames = m , myconst=cs}

getConstants :: QState (M.Map Name ELExp)
getConstants = undefined

nothing :: QState a
nothing = QState $ MaybeT { runMaybeT = return Nothing }

isMaybe :: QState a -> QState (Maybe a)
isMaybe (QState m) = QState $ MaybeT { runMaybeT = do
    m' <- runMaybeT m
    case m' of
      Nothing -> return Nothing
      Just a  -> return $ Just (Just a)
  }

runQState :: Q a -> QState a
runQState q = QState (S.lift . S.StateT $ \m -> q >>= \a -> return (a,m))

runStateQ :: QState a -> M.Map Name Ident -> Q (Maybe a)
runStateQ (QState st) m = S.evalStateT (runMaybeT st) (initState m)

initState :: M.Map Name Ident -> MyState
initState m = MyState { mynames=m, myconst=M.fromList [] }
-- constants :: M.Map Name (Q Exp)
-- constants = M.fromList $ [ (mkName "put", [|put|]) 
--                          , (mkName "(>!)", ]


-- freshNat min ls returns the smallest nat >= min that is not in ls
freshNat :: Nat -> [Nat] -> Nat
freshNat min [] = min
freshNat min (min' : ls) = if min < min' then min
                           else freshNat min' ls

fresh :: QState Nat
fresh = do
  m  <- getMap
  return $ freshNat Z $ M.elems m

transformPat :: Pat -> QState Pattern
transformPat (VarP n) = do
  x <- fresh
  m <- getMap
  putMap $ M.insert n x m
  return $ PVar x
transformPat (TupP ps) = do
  ps' <- mapM transformPat ps
  return $ PTuple ps'
transformPat _ = error "Other pattern"

transformPats :: [Pat] -> QState [Pattern]
transformPats [] = return []
transformPats (p : ps) = do
  p'  <- transformPat p 
  ps' <- transformPats ps
  return $ p':ps'

transformLam :: Pattern -> Exp -> QState Exp
transformLam (PVar x) e = do
  case natToS x of { NatSS x' -> do
    ex <- runQState [|x'|]
    return $ AppE (AppE (VarE $ mkName "abs") ex) e
  } 
transformLam (PTuple ps) e = do
  x <- fresh
  case natToS x of { NatSS x' -> do
    ex <- runQState [|x'|]
 -- λ x. case x of p -> e
    return $ (VarE $ mkName "abs") 
             `AppE` ex
             `AppE` ( (VarE $ mkName "caseof")
                      `AppE` ex
                      `AppE` e )
  }
transformLams :: [Pattern] -> Exp -> QState Exp
transformLams []     e = return e
transformLams [p]    e = transformLam p e
transformLams (p:ps) e = do
  e' <- transformLams ps e
  transformLam p e'

transform :: Exp -> QState Exp
transform (VarE n)          = do
  m <- getMap
  case M.lookup n m of
    Just x  -> do -- [| e |] >>= \e -> return (e,m)
      vName <- return $ mkName "Var"
      pf    <- case natToS x of NatSS x' -> runQState [| singS x' |]
      return $ AppE (ConE vName) pf
    Nothing -> nothing
transform (LamE pats e)     = do
  e'    <- transform e
  ps    <- transformPats pats
  transformLams ps e'
transform (TupE es)         = undefined

transform (ConE n)          = undefined
transform (LitE l)          = undefined
transform (AppE e1 e2)      = undefined
transform (InfixE e1 e e2)  = undefined
transform (UInfixE e1 e e2) = undefined
transform (ParensE e)       = undefined
transform (LamCaseE matches)= undefined
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

suspendTH :: QuasiQuoter 
suspendTH = QuasiQuoter { quoteExp  = suspendE
                        , quotePat  = undefined
                        , quoteType = undefined
                        , quoteDec  = undefined }

suspendE :: String -> Q Exp
suspendE = undefined


transformTH :: Q Exp -> Q Exp
transformTH m = do
  e <- m 
  me <- runStateQ (transform e) M.empty
  return $ AppE (VarE $ mkName "suspend") $ fromMaybe e me
  
