-- Copyright (c) A Karlsson 2010
-- Copyright (c) T Olausson 2010
module Data.Binary.BitString.BitGet where

import Data.Binary.BitString.BitString as BS

import Control.Monad
import Data.Int
import Data.Word
import Prelude hiding (drop, head, splitAt)
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Applicative

data FileStatus = EOF | BOF -- End of file and beginning of file
    deriving (Eq, Show)

newtype BitGetT m a = BitGetT { unGet :: BitString -> m (a, BitString) }
type BitGet = BitGetT Identity

instance (Monad m) => Functor (BitGetT m) where
    fmap f m = BitGetT $ \s -> do 
        ~(x,s') <- unGet m s
        return (f x, s')

instance MonadTrans BitGetT where
    lift m = BitGetT $ \s -> do
        a <- m
        return (a,s)

instance (Monad m) => Monad (BitGetT m) where
    return a = BitGetT $ \bs -> return (a,bs)
    bg >>= f = BitGetT $ \bs -> do
        ~(a,bs') <- unGet bg bs
        unGet (f a) bs'

instance (Monad m) => Applicative (BitGetT m) where
    pure a = return a
    (<*>) = ap

runBitGet :: BitGet a -> BitString -> a
runBitGet g bs = case runIdentity (unGet g bs) of
    (a, _) -> a

runBitGetT :: Monad m => BitGetT m a -> BitString -> m a
runBitGetT g bs = liftM fst (unGet g bs)

get :: (Monad m) => BitGetT m BitString
get = BitGetT $ \bs -> return (bs,bs)

put :: (Monad m) => BitString -> BitGetT m ()
put bs = BitGetT $ const $ return ((),bs)

getBit :: (Monad m) => BitGetT m Bool
getBit = do r <- getAsWord8 1
            return $ r == 1

getBits :: (Monad m) => Int64 -> BitGetT m BitString
getBits i = do
    (bits,rest) <- liftM (splitAt i) get
    put rest
    return bits

-- YEAHH HASKELL!!
skip :: (Monad m) => Int64 -> BitGetT m ()
skip i = (liftM (drop i) get) >>= put

-- will return true when it was possible to skip this many bits
safeSkip :: (Monad m) => Int64 -> BitGetT m FileStatus
safeSkip i = do
    bis <- get
    case BS.safeDrop i bis of
        Just bs' -> put bs' >> return BOF
        Nothing  -> return EOF

getWord8 :: (Monad m) => BitGetT m Word8
getWord8 = getAsWord8 8

getWord16 :: (Monad m) => BitGetT m Word16
getWord16 = getAsWord16 16

getAsWord8 :: (Monad m) => Int64 -> BitGetT m Word8
getAsWord8 i = do
    r <- liftM (BS.takeAsWord8 (fromIntegral i)) get
    skip i
    return r

getAsWord16 :: (Monad m) => Int64 -> BitGetT m Word16
getAsWord16 i = do
    r <- liftM (BS.takeAsWord16 (fromIntegral i)) get
    skip i
    return r

lookAhead :: (Monad m) => BitGetT m a -> BitGetT m a
lookAhead bg = do
    s <- get
    res <- bg
    put s
    return res
 
getRemaining :: (Monad m) => BitGetT m BitString
getRemaining = get

getInt :: (Monad m) => Int64 -> BitGetT m Int
getInt i = do
    s <- liftM (BS.getInt i) get
    skip i
    return s

getLength :: (Monad m) => BitGetT m Int64
getLength = liftM BS.length get

getAtLeast :: (Monad m) => Int64 -> BitGetT m Bool
getAtLeast i = liftM (flip BS.atLeast i) get
