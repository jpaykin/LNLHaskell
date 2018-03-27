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
import Prelude hiding (read, (^), take)
import Control.Monad (forM_)

import Types
import Classes
import Interface
import DeepEmbedding as D
import ShallowEmbedding as S

-- Signature 

--data LType where
--  One :: LType
--  Tensor :: LType -> LType -> LType
--  Lolli :: LType -> LType -> LType
--  Lower :: Type -> LType

data FHSig sig = FHSig
type Handle = MkLType 'FHSig

class HasMILL sig => HasFH sig where
  open :: String -> LExp sig Empty Handle
  read :: LExp sig γ Handle -> LExp sig γ (Handle ⊗ Lower Char)
  write :: LExp sig γ Handle -> Char -> LExp sig γ Handle
  close :: LExp sig γ Handle -> LExp sig γ One

type instance Effect _ = IO
data instance LVal _ Handle = VHandle (IO.Handle)

instance HasFH Shallow where
  open s  = SExp $ \ρ -> VHandle <$> IO.openFile s IO.ReadWriteMode
  read e  = SExp $ \ρ -> do VHandle h <- runSExp e ρ
                            c <- IO.hGetChar h
                            return $ S.VPair (VHandle h) (S.VPut c)
  write e c = SExp $ \ρ → do VHandle h <- runSExp e ρ
                             IO.hPutChar h c
                             return $ VHandle h
  close e = SExp $ \ρ -> do VHandle h <- runSExp e ρ 
                            IO.hClose h
                            return S.VUnit
                             
data FHExp :: Sig -> Exp where
  Open :: String -> FHExp sig Empty Handle
  Read :: LExp sig γ Handle -> FHExp sig γ (Handle ⊗ Lower Char)
  Write :: LExp sig γ Handle -> Char -> FHExp sig γ Handle
  Close :: LExp sig γ Handle -> FHExp sig γ One

instance Domain Deep FHExp where
  evalDomain (Open s)    _ = VHandle <$> IO.openFile s IO.ReadWriteMode
  evalDomain (Read e)    ρ = do VHandle h <- eval e ρ
                                c <- IO.hGetChar h
                                return $ D.VPair (VHandle h) (D.VPut c)
  evalDomain (Write e c) ρ = do VHandle h <- eval e ρ
                                IO.hPutChar h c
                                return $ VHandle h
  evalDomain (Close e)   ρ = do VHandle h <- eval e ρ
                                IO.hClose h
                                return D.VUnit
                                

-- Examples ----------------------------------


writeString :: HasFH sig => String -> LExp sig γ Handle -> LExp sig γ Handle
writeString s e = foldl write e s

readWriteTwice :: HasFH sig => LExp sig Empty (Handle ⊸ Handle)
readWriteTwice = λ $ \h -> read h `letPair` \(h,x) ->
                           x >! \c ->
                           writeString [c,c] h

withFile :: HasFH sig => String -> Lift sig (Handle ⊸ Handle ⊗ Lower a) -> Lin sig a
withFile name f = suspend $ (force f ^ open name) `letPair` \(h,a) -> 
                            close h `letUnit` a

readM :: HasFH sig => LExp sig Empty (LState Handle (Lower Char))
readM = λ read

writeM :: HasFH sig => Char -> LExp sig Empty (LState Handle One)
writeM c = λ $ \h -> write h c ⊗ unit

readWriteTwiceM :: HasFH sig => Lift sig (LState Handle One)
readWriteTwiceM = suspend $ readM    =>>= (λbang $ \c ->
                            writeM c =>>= (λunit $ \() -> writeM c))

readT :: HasFH sig => LStateT sig Handle Char
readT = suspend readM

writeT :: HasFH sig => Char -> LStateT sig Handle ()
writeT c = suspend $ writeM c =>>= (λunit $ \() -> lpure $ put ())

readWriteTwiceT :: HasFH sig => LStateT sig Handle ()
readWriteTwiceT = do c <- readT
                     writeT c
                     writeT c

take :: HasFH sig => Int -> LStateT sig Handle String
take n | n <= 0    = return ""
take n | otherwise = do c <- readT
                        s <- take (n-1)
                        return $ c:s

writeStringT :: HasFH sig => String -> LStateT sig Handle ()
writeStringT s = forM_ s writeT

withFileT :: HasFH sig => String -> LStateT sig Handle a -> Lin sig a
withFileT name st = evalLStateT st (suspend $ open name) (suspend $ λ close)

test :: Lin Shallow String
test = do withFileT "foo" $ writeStringT "Hello world!"
          withFileT "foo" $ take 7
