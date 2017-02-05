{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module FileHandles where

import qualified System.IO as IO
import Data.Proxy

import Types
import Context
import Lang
import Interface

-- Signature

data FHSig sig = FHSig
type Handle = ('LType (InSig FHSig sig) 'FHSig :: LType sig)

data FHLExp lang g τ where
  Open      :: String -> FHLExp lang 'Empty Handle
  ReadLine  :: LExp lang g Handle -> FHLExp lang g (Handle ⊗ Lower String)
  WriteLine :: LExp lang g Handle -> String -> FHLExp lang g Handle
  Close     :: LExp lang g Handle -> FHLExp lang g One

data FHLVal lang τ where
  VHandle :: IO.Handle -> FHLVal lang Handle

type FHDom = '(FHLExp, FHLVal)
proxyFH = (Proxy :: Proxy FHDom)

type HasFHDom (lang :: Lang sig) = 
    ( WFDomain FHDom lang
    , Domain OneDom lang, Domain TensorDom lang
    , Domain LowerDom lang, Domain LolliDom lang
    , SigEffect sig ~ IO
    )

instance HasFHDom lang => Domain FHDom lang where
  evalDomain SEmpty (Open s) = do
    h <- IO.openFile s IO.ReadWriteMode
    return $ vhandle h
  evalDomain ρ (ReadLine e) = do
    VHandle h <- evalToValDom proxyFH ρ e
    IO.hFlush h
    s <- IO.hGetLine h
    return $ vhandle h `vpair` vput s
  evalDomain ρ (WriteLine e s) = do
    VHandle h <- evalToValDom proxyFH ρ e
    IO.hPutStrLn h s
    return $ vhandle h
  evalDomain ρ (Close e) = do
    VHandle h <- evalToValDom proxyFH ρ e
    return vunit


vhandle :: HasFHDom lang => IO.Handle -> LVal lang Handle
vhandle = VDom proxyFH . VHandle

open :: HasFHDom lang 
     => String -> Lift lang Handle
open s = Suspend . Dom proxyFH $ Open s

readLine :: HasFHDom lang
         => LinT lang (LState' Handle) String
readLine = suspendT . λ $ \h -> Dom proxyFH (ReadLine h)

writeLine :: HasFHDom lang
          => String -> LinT lang (LState' Handle) ()
writeLine s = suspendT . λ $ \h -> 
  Dom proxyFH (WriteLine h s) `letin` \h ->
  h ⊗ put ()

close :: HasFHDom lang
      => Lift lang (Handle ⊸ One)
close = Suspend . λ $ \ h -> Dom proxyFH (Close h)


instance Show (FHLExp lang g τ) where
  show (Open s)     = "Open " ++ show s
  show (ReadLine h) = "ReadLine(" ++ show h ++ ")"
  show (WriteLine h s) = "WriteLine(" ++ show h ++ ", " ++ show s ++ ")"
  show (Close h)       = "Close(" ++ show h ++ ")"


-- Examples

withFile :: HasFHDom lang 
         => String -> LinT lang (LState' Handle) a -> Lin lang a
withFile s f = evalLState f (open s) close

type MyFHSig = ( 'Sig IO '[ FHSig, TensorSig, OneSig, LowerSig, LolliSig ] :: Sig)
type MyFHDom = ( 'Lang '[ FHDom, TensorDom, OneDom, LowerDom, LolliDom ] :: Lang MyFHSig )

ex1 :: Lin MyFHDom String
ex1 = withFile "helloworld.txt" $ do
        x <- readLine
        y <- readLine
        z <- readLine
        writeLine "Anyway3"
        return $ x ++ y ++ z
        
