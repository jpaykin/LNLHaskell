{-# LANGUAGE UnicodeSyntax, DataKinds, TypeOperators, KindSignatures,
             TypeInType, GADTs, MultiParamTypeClasses, FunctionalDependencies,
             TypeFamilies, AllowAmbiguousTypes, FlexibleInstances,
             UndecidableInstances, InstanceSigs, TypeApplications, 
             ScopedTypeVariables, ConstraintKinds, LambdaCase,
             EmptyCase, RankNTypes, FlexibleContexts, TypeFamilyDependencies
#-}

module ByteString where

import Prelude hiding (read,(^),drop,head,uncurry)

import Types
import Interface
import Classes
import ShallowEmbedding

import Foreign.ForeignPtr
import Data.Word8
import Control.Monad
import Data.Maybe

data ByteStringSig sig = HeapSig | BufferSig | PtrSig
type Buffer = MkLType 'BufferSig
type Ptr = MkLType 'PtrSig

-- TODO: factor this class into one for the heap operations, one for buffers
class HasMILL sig => HasByteString sig where
  alloc :: Int -- bytes to allocate
        -> LExp sig Empty Ptr
  peek :: LExp sig γ (Ptr ⊸ Ptr ⊗ Lower Word8)
  poke :: LExp sig γ (Lower Word8 ⊸ Ptr ⊸ Ptr)
  free :: LExp sig Empty (Ptr ⊸ One)

  -- memcopy ::  Int ⊸ Int ⊸ Int ⊸ Ptr ⊸ Ptr ⊸ Ptr ⊗ Ptr
  -- memcopy o1 o2 len p1 p2 replicates p1+o1+length bytes into p2+o2
  memcopy :: Int -> Int -> Int -> LExp sig Empty (Ptr ⊸ Ptr ⊸ Ptr ⊗ Ptr)
  memmove :: Int -> Int -> Int -> LExp sig Empty (Ptr ⊸ Ptr ⊸ Ptr)
  memset :: Int -> Int -> Word8 -> LExp sig Empty (Ptr ⊸ Ptr)

  empty  :: LExp sig Empty Buffer
  size   :: LExp sig Empty (Buffer ⊸ Buffer ⊗ Lower Int)
  is_null :: LExp sig Empty (Buffer ⊸ Buffer ⊗ Lower Bool)
  head   :: LExp sig Empty (Buffer ⊸ Buffer ⊗ Lower (Maybe Word8))
  cons   :: Word8 -> LExp sig Empty (Buffer ⊸ Buffer)
  append :: LExp sig Empty (Buffer ⊸ Buffer ⊸ Buffer ⊗ Buffer)
  free_buffer :: LExp sig Empty (Buffer ⊸ One)


-- Monad transformer versions of some of the library operations
-- Note: LStateT sig σ α is a non-linear (ordinary) monad
-- with a linear state of type σ, returning a non-linear value of type α
sizeT :: HasByteString sig => LStateT sig Buffer Int
sizeT = suspend size

is_nullT :: HasByteString sig => LStateT sig Buffer Bool
is_nullT = suspend is_null

headT :: HasByteString sig => LStateT sig Buffer (Maybe Word8)
headT = suspend head

consT :: HasByteString sig => Word8 -> LStateT sig Buffer ()
consT = lstate1 . suspend . cons

-- not sure how often we will want this
appendT :: HasByteString sig => LStateT sig (Buffer ⊗ Buffer) ()
appendT = lstate1 . suspend $ uncurry append

-- free_append b1 b2 appends b2 to b1 and deallocates b2
free_append :: HasByteString sig 
            => LExp sig Empty (Buffer ⊸ Buffer ⊸ Buffer)
free_append = λ $ \b1 → λ $ \b2 ->
              append ^ b1 ^ b2 `letPair` \(b1,b2) ->
              free_buffer ^ b2 `letUnit` b1

free_appendT :: HasByteString sig
             => Lift sig Buffer -> LStateT sig Buffer ()
free_appendT b1 = lstate1 . suspend $ λ $ \b2 → 
                            free_append ^ force b1 ^ b2


-- do we want singleton, pack, etc, to be build-in for a more effient implementation?
singleton :: HasByteString sig => Word8 -> Lift sig Buffer
singleton w = Suspend $ cons w ^ empty

cons' :: (HasByteString sig, WFCtx γ)
      => LExp sig γ Buffer ->  Word8 -> LExp sig γ Buffer
cons' b w = cons w ^ b

pack :: HasByteString sig => [Word8] -> Lift sig Buffer
pack ls = Suspend $ foldl cons' empty ls

unpackT :: HasByteString sig => LStateT sig Buffer [Word8]
unpackT = do n ← sizeT
             ls ← replicateM n headT
             return $ catMaybes ls

unpack :: HasByteString sig => Lift sig Buffer -> Lin sig [Word8]
unpack b = evalLStateT unpackT b (suspend free_buffer)

    
