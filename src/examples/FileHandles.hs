module FileHandles where

import qualified System.IO as IO
--import Data.Proxy
import Prelude hiding (read, (^), take)
import Control.Monad (forM_)

import Types
--import Classes
import Interface
import DeepEmbedding as D
import ShallowEmbedding as S

-- Signature 

--data LType where
--  One :: LType
--  Tensor :: LType -> LType -> LType
--  Lolli :: LType -> LType -> LType
--  Lower :: Type -> LType

data FHSig exp = FHSig
type Handle = MkLType 'FHSig

class HasMILL exp => HasFH exp where
  open :: String -> exp '[] Handle
  read :: exp γ Handle -> exp γ (Handle ⊗ Lower Char)
  write :: exp γ Handle -> Char -> exp γ Handle
  close :: exp γ Handle -> exp γ One

type instance Effect _ = IO
data instance LVal _ Handle = VHandle (IO.Handle)

instance HasFH Shallow where
  open s  = SExp $ \_ -> VHandle <$> IO.openFile s IO.ReadWriteMode
  read e  = SExp $ \ρ -> do VHandle h <- runSExp e ρ
                            c <- IO.hGetChar h
                            return $ S.VPair (VHandle h, S.VPut c)
  write e c = SExp $ \ρ → do VHandle h <- runSExp e ρ
                             IO.hPutChar h c
                             return $ VHandle h
  close e = SExp $ \ρ -> do VHandle h <- runSExp e ρ 
                            IO.hClose h
                            return $ S.VUnit ()
                             
data FHExp :: Sig -> Sig where
  Open :: String -> FHExp exp '[] Handle
  Read :: exp γ Handle -> FHExp exp γ (Handle ⊗ Lower Char)
  Write :: exp γ Handle -> Char -> FHExp exp γ Handle
  Close :: exp γ Handle -> FHExp exp γ One

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


writeString :: HasFH exp => String -> exp γ Handle -> exp γ Handle
writeString s e = foldl write e s

readWriteTwice :: HasFH exp => exp '[] (Handle ⊸ Handle)
readWriteTwice = λ $ \h -> read h `letPair` \(h,x) ->
                           x >! \c ->
                           writeString [c,c] h

withFile :: HasFH exp => String -> Lift exp (Handle ⊸ Handle ⊗ Lower a) -> Lin exp a
withFile name f = suspend $ (force f ^ open name) `letPair` \(h,a) -> 
                            close h `letUnit` a

readM :: HasFH exp => exp '[] (LState Handle (Lower Char))
readM = λ read

writeM :: HasFH exp => Char -> exp '[] (LState Handle One)
writeM c = λ $ \h -> write h c ⊗ unit

readWriteTwiceM :: HasFH exp => Lift exp (LState Handle One)
readWriteTwiceM = suspend $ readM    =>>= (λbang $ \c ->
                            writeM c =>>= (λunit $ \() -> writeM c))

readT :: HasFH exp => LStateT exp Handle Char
readT = suspend readM

writeT :: HasFH exp => Char -> LStateT exp Handle ()
writeT c = suspend $ writeM c =>>= (λunit $ \() -> lpure $ put ())

readWriteTwiceT :: HasFH exp => LStateT exp Handle ()
readWriteTwiceT = do c <- readT
                     writeT c
                     writeT c

take :: HasFH exp => Int -> LStateT exp Handle String
take n | n <= 0    = return ""
take n | otherwise = do c <- readT
                        s <- take (n-1)
                        return $ c:s

writeStringT :: HasFH exp => String -> LStateT exp Handle ()
writeStringT s = forM_ s writeT

withFileT :: HasFH exp => String -> LStateT exp Handle a -> Lin exp a
withFileT name st = evalLStateT st (suspend $ open name) (suspend $ λ close)

test :: Lin Shallow String
test = do withFileT "foo" $ writeStringT "Hello world!"
          withFileT "foo" $ take 7
