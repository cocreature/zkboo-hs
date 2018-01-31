{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Crypto.ZKBoo.Util
  ( ZN
  , RandomElement(..)
  , randomNumber
  , FromBytes(..)
  , ToBytes(..)
  ) where

import           Crypto.Number.Basic (numBytes)
import           Crypto.Number.Serialize (os2ip, i2ospOf_)
import           Crypto.Random
import           Data.ByteString (ByteString)
import qualified ByteString.StrictBuilder as ByteString
import           Data.Proxy
import           GHC.TypeLits


-- | Generate a random number in range [0, n).
--
-- We want to avoid modulo bias, so we use the arc4random_uniform
-- implementation (http://stackoverflow.com/a/20051580/615030). Specifically,
-- we repeatedly generate a random number in range [0, 2^x) until we hit on
-- something outside of [0, 2^x mod n), which means that it'll be in range
-- [2^x mod n, 2^x). The amount of numbers in this interval is guaranteed to
-- be divisible by n, and thus applying 'mod' to it will be safe.
--
-- Stolen from https://github.com/input-output-hk/cardano-sl/blob/400157238d234fd1cfcb0c29c596326287d7c698/crypto/Pos/Crypto/Random.hs#L40
randomNumber :: MonadRandom m => Integer -> m Integer
randomNumber n
    | n <= 0 = error "randomNumber: n <= 0"
    | otherwise = gen
  where
    size = max 4 (numBytes n)             -- size of integers, in bytes
    rangeMod = 2 ^ (size * 8) `rem` n     -- 2^x mod n
    gen = do
        x <- (os2ip :: ByteString -> Integer) <$> getRandomBytes size
        if x < rangeMod then gen else return (x `rem` n)

-- | ℤ/nℤ
newtype ZN (n :: Nat) = ZN Integer
  deriving (Eq, Ord, Show)


instance KnownNat n => Num (ZN n) where
  ZN a + ZN b = ZN ((a + b) `mod` natVal (Proxy :: Proxy n))
  ZN a - ZN b = ZN ((a - b) `mod` natVal (Proxy :: Proxy n))
  ZN a * ZN b = ZN ((a * b) `mod` natVal (Proxy :: Proxy n))
  abs i = i
  signum (ZN i) = ZN (signum i)
  fromInteger i = ZN (i `mod` natVal (Proxy :: Proxy n))

instance KnownNat n => RandomElement (ZN n) where
  randomElement = ZN <$> randomNumber (natVal (Proxy :: Proxy n))

instance KnownNat n => ToBytes (ZN n) where
  toBytes (ZN i) = i2ospOf_ (numBytes (natVal (Proxy :: Proxy n))) i
  byteLength _ = numBytes (fromIntegral (natVal (Proxy :: Proxy n)))

instance FromBytes (ZN n) where
  fromBytes bs = ZN (os2ip bs)

-- | Class for types from which elements can be drawn uniformly at random.
class RandomElement f where
  -- | This should give back an element selected uniformly at random from all values of type 'f'.
  -- Instances should thus only be created for types with a finite number of inhabitants.
  randomElement :: MonadRandom m => m f

-- | Class for types whose elements can be converted to fixed-length byte strings.
class ToBytes f where
  -- | Convert an element to 'ByteString.Builder'. The length must be independent of the element.
  toBytesBuilder :: f -> ByteString.Builder
  toBytesBuilder = ByteString.bytes . toBytes
  -- | Convert an element to a 'ByteString'. The length must be independent of the element
  --
  -- Note that in most cases it is more efficient to implement 'toBytesBuilder' instead.
  toBytes :: f -> ByteString
  toBytes = ByteString.builderBytes . toBytesBuilder
  -- | The length in bytes
  byteLength :: proxy f -> Int

-- | Class for types whose elemnts can be deserialized from fixed-length byte strings.
class FromBytes f where
  fromBytes :: ByteString -> f
