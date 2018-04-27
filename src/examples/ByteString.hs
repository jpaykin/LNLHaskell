module ByteString where

import Prelude hiding (read,(^),drop,head,uncurry)

import Types
import Interface
import Classes
-- import ShallowEmbedding

-- import Foreign.ForeignPtr
import Data.Word8
import Control.Monad
import Data.Maybe

data ByteStringSig exp = BufferSig | PtrSig
type Buffer = MkLType 'BufferSig
type Ptr = MkLType 'PtrSig

-- TODO: factor this class into one for the heap operations, one for buffers
class HasMILL exp => HasByteString exp where
  alloc :: Int -- bytes to allocate
        -> exp '[] Ptr
  peek :: exp γ (Ptr ⊸ Ptr ⊗ Lower Word8)
  poke :: exp γ (Lower Word8 ⊸ Ptr ⊸ Ptr)
  free :: exp '[] (Ptr ⊸ One)

  -- memcopy ::  Int ⊸ Int ⊸ Int ⊸ Ptr ⊸ Ptr ⊸ Ptr ⊗ Ptr
  -- memcopy o1 o2 len p1 p2 replicates p1+o1+length bytes into p2+o2
  memcopy :: Int -> Int -> Int -> exp '[] (Ptr ⊸ Ptr ⊸ Ptr ⊗ Ptr)
  memmove :: Int -> Int -> Int -> exp '[] (Ptr ⊸ Ptr ⊸ Ptr)
  memset :: Int -> Int -> Word8 -> exp '[] (Ptr ⊸ Ptr)

  empty   :: exp '[] Buffer
  size    :: exp '[] (Buffer ⊸ Buffer ⊗ Lower Int)
  is_null :: exp '[] (Buffer ⊸ Buffer ⊗ Lower Bool)
  head    :: exp '[] (Buffer ⊸ Buffer ⊗ Lower (Maybe Word8))
  cons    :: Word8 -> exp '[] (Buffer ⊸ Buffer)
  append  :: exp '[] (Buffer ⊸ Buffer ⊸ Buffer ⊗ Buffer)
  free_buffer :: exp '[] (Buffer ⊸ One)

-- is Lin a Hask monad transformer

-- Monad transformer versions of some of the library operations
-- Note: LStateT exp σ α is a non-linear (ordinary) monad
-- with a linear state of type σ, returning a non-linear value of type α
                             -- Lift (Buffer ⊸ Buffer ⊗ Lower Int)
sizeT :: HasByteString exp => LStateT exp Buffer Int
sizeT = suspend size

is_nullT :: HasByteString exp => LStateT exp Buffer Bool
is_nullT = suspend is_null

headT :: HasByteString exp => LStateT exp Buffer (Maybe Word8)
headT = suspend head

consT :: HasByteString exp => Word8 -> LStateT exp Buffer ()
consT = lstate1 . suspend . cons

-- not sure how often we will want this
appendT :: HasByteString exp => LStateT exp (Buffer ⊗ Buffer) ()
appendT = lstate1 . suspend $ uncurry append

-- free_append b1 b2 appends b2 to b1 and deallocates b2
free_append :: HasByteString exp 
            => exp '[] (Buffer ⊸ Buffer ⊸ Buffer)
free_append = λ $ \b1 → λ $ \b2 ->
              append ^ b1 ^ b2 `letPair` \(b1,b2) ->
              free_buffer ^ b2 `letUnit` b1

free_appendT :: HasByteString exp
             => Lift exp Buffer -> LStateT exp Buffer ()
free_appendT b1 = lstate1 . suspend $ λ $ \b2 → 
                            free_append ^ force b1 ^ b2


-- do we want singleton, pack, etc, to be build-in for a more effient implementation?
singleton :: HasByteString exp => Word8 -> Lift exp Buffer
singleton w = Suspend $ cons w ^ empty

cons' :: (HasByteString exp, WFCtx γ, KnownDomain γ)
      => exp γ Buffer ->  Word8 -> exp γ Buffer
cons' b w = cons w ^ b

pack :: HasByteString exp => [Word8] -> Lift exp Buffer
pack ls = Suspend $ foldl cons' empty ls

unpackT :: HasByteString exp => Int -> LStateT exp Buffer [Word8]
unpackT n = do ls ← replicateM n headT
               return $ catMaybes ls

unpack :: HasByteString exp => Int -> Lift exp Buffer -> Lin exp [Word8]
unpack n b = evalLStateT (unpackT n) b (suspend free_buffer)

    
