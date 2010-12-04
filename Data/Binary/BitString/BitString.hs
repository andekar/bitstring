-- Copyright (c) A Karlsson 2010 
-- Copyright (c) T Olausson 2010
module Data.Binary.BitString.BitString where

-- This library provides a pure interface to bits, similar to the monadic
-- BitGet library. This version uses lazy bytestrings.
-- All numeric arguments are in bits, not in bytes.

import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Internal as LI
import qualified Data.ByteString as S

import Data.Int
import Data.Word
import Data.Bits
import Prelude hiding (drop, head, length, take, drop, splitAt, tail, concat)
import Control.Monad (liftM)
import qualified Data.List as List
import Control.Arrow
import Debug.Trace

type Bit = Bool

fi :: (Integral a, Num b) => a -> b
fi = fromIntegral

-- This looks very much like the internals of ByteString.Lazy, with the added
-- Word8s that keeps track of bits in the first byte and the last byte.
-- *invariant* If the BitString is a Chunk, then the bytestring in it is never
--  empty
data BitString = Empty | Chunk L.ByteString !Word8 !Word8 BitString
    deriving Show

-- Creates an empty BitString.
empty :: BitString
empty = Empty

-- Converts a Lazy ByteString to a BitString.
convert :: L.ByteString -> BitString
convert bs = Chunk bs 0 0 Empty

-- Converts and specifies a starting index, which may be larger than 8.
-- convertAt :: L.ByteString -> Int64 -> BitString
-- convertAt bs i = Chunk (L.drop (i `div` 8) bs) (fi $ i `mod` 8) 0 empty

-- Similar to pack in ByteString
convertWords :: [Word8] -> BitString
convertWords ws = Chunk (L.pack ws) 0 0 Empty

-- Lazily reads a file into a BitString
readFile :: FilePath -> IO BitString
readFile = liftM convert . L.readFile

-- Concat a list of BitStrings
concat :: [BitString] -> BitString
concat [] = empty
concat xs = List.foldl append empty xs

-- Append a BitString onto another.
append :: BitString -> BitString -> BitString
append Empty ys = ys
append (Chunk xs f b rest) ys = Chunk xs f b (append rest ys) 

-- Indexing in a BitString gives a Bit
index :: Int64 -> BitString -> Bit
index i bs = head $ drop i bs

-- The first bit in the BitString
head :: BitString -> Bit
head Empty = error "BitString.head: empty string"
head c = testBit (takeAsWord8 1 c) 0

-- All but the first bit in the BitString
tail :: BitString -> BitString
tail Empty = error "BitString.tail: empty string"
tail bs = drop 1 bs

-- take is implemented as fst . splitAt
take :: Int64 -> BitString -> BitString
take i bs = fst $ splitAt i bs

takeWord8 :: BitString -> Word8
takeWord8 = takeAsWord8 8

takeWord16 :: BitString -> Word16
takeWord16 bs = (shiftL 8 $ fi l) .|. fi r
    where (l, r) = takeWord8 *** takeWord8 $ splitAt 8 bs

-- Here magic happens
takeAsWord8 :: Int -> BitString -> Word8
takeAsWord8 _ Empty = 0
takeAsWord8 0 _ = 0
takeAsWord8 i bis
    | i > 8 = error $ "Too big to make any sense " ++ show i
    | not (atLeastBS bs (fi i + fb f b))
    = let r = takeAsWord8 (fi i - ((fi (L.length bs) * 8)
                                   - fb f b)) rest
          len = length m
          s = L.head $ flip right (max (8 - i) (8 - fi len)) $
              left (right bs b) (fi f + fi b)
      in s .|. r
    | i + fi f <= 8
    = L.head $ flip right (8-i) $ left bs f
    | otherwise = L.head $ flip right (8-i) $
                  left bs f
    where (m@(Chunk bs f b rest), _) = splitAt (fi i) bis
          left bs f = leftShiftByteString (fi f) bs
          right bs b = rightShiftByteString (fi b) bs
          fb f b = fi f + fi b

bss = Chunk (L.pack [0]) 0 0 (Chunk (L.pack [0x40]) 0 0 Empty)

takeAsWord16 :: Int -> BitString -> Word16
takeAsWord16 i bis
    | i > 16 = error "way WAY too much to put in Word16!"
    | i <= 8 = fi $ takeAsWord8 i bis
    | otherwise = (fi l `shiftL` m) .|. fi r
    where (l, r) = takeAsWord8 8 *** takeAsWord8 m $ splitAt 8 bis
          m = i `mod` 8

-- this will construct an rightshifted result!
-- this might need shifting and stuff later!
getInt :: Int64 -> BitString -> Int
getInt _ Empty = 0
getInt 0 _     = 0
getInt i bs    = let (Chunk r f b _) = take i bs
                     r' = rightShiftByteString (fi f) $
                          rightShiftByteString (fi b) $
                          leftShiftByteString (fi f) r
                 in fi $ shiftBytes 0 $ map fi $ L.unpack r'
    where shiftBytes :: Word32 -> [Word8] -> Word32
          shiftBytes w []     = w
          shiftBytes w (x:xs) = flip shiftBytes xs $ (shiftL w 8) .|. fi x

-- drop is implemented as snd . splitAt
drop :: Int64 -> BitString -> BitString
drop = snd `dot` splitAt

safeDrop :: Int64 -> BitString -> Maybe BitString
safeDrop i bs = if atLeast bs i then Just (drop i bs) else Nothing

dot = (.) . (.)

-- Checks if a BitString is empty
null :: BitString -> Bool
null Empty = True
null _ = False

-- Splits a BitString into two parts.
-- This function is truly the most complicated in the library
splitAt :: Int64 -> BitString -> (BitString, BitString)
splitAt i Empty = (Empty, Empty)
splitAt 0 r     = (Empty, r)
splitAt i bs@(Chunk lb f b rest)
    | atLeastBS lb (fi f + i + fi b) =
        let fst'  = L.take fstLen lb
            snd'  = L.drop sndLen lb
            sndch = if L.null snd' || ((not $ atLeastBS snd' 16) && (f' + b == 8))
                        then rest
                        else Chunk snd' f' b rest
        in (Chunk fst' f ((8 - f') `mod` 8) Empty, sndch)

    -- These cases should work...NOT extensively tested though :(
    | atLeast bs i =
         let (left, s) = splitAt (i - ((L.length lb * 8) - (fi $ f + b))) rest
         in  (Chunk lb f b left, s)
    | otherwise = (bs, Empty)
  where
    fstLen = (i + fi f + 7) `div` 8
    sndLen = (i + fi f) `div` 8
    f' = fi $ (fi f + i) `mod` 8

-- Strictly checks the length of a BitString
length :: BitString -> Int64
length Empty = 0
length (Chunk bs f b rest)
    = (fi (L.length bs * 8) - fi (f + b)) + length rest

-- Lazily checks if the BitString is at least j bits.
atLeast :: BitString -> Int64 -> Bool
atLeast Empty 0 = True
atLeast Empty _ = False
atLeast (Chunk (LI.Chunk sb lb) f b rest) i
    | i <= sblen = True
    | atLeastBS lb (i - sblen) = True
    | otherwise = atLeast rest (i - sblen - L.length lb)
  where
--     sblen :: Int64
    sblen = (fi $ S.length sb) * 8 - fi (f+b)

-- Functions below are not exported, but only used internally
-- Some of these are taken from Binary.Strict.BitGet

-- this function will under no circumstances be exported out of this module!!!
atLeastBS :: L.ByteString -> Int64 -> Bool
atLeastBS LI.Empty 0 = True
atLeastBS LI.Empty _ = False
atLeastBS (LI.Chunk sb lb) i
    | i <= fi (S.length sb * 8) = True
    | otherwise = atLeastBS lb (i - (fi $ S.length sb) * 8)

-- Taken from the BitGet library, just altered for lazy bytestrings
rightShiftByteString :: Int -> L.ByteString -> L.ByteString
rightShiftByteString 0 = id
rightShiftByteString n = snd . L.mapAccumL f 0
 where
  f acc b = (b .&. (bottomNBits n), (b `shiftR` n) .|. (acc `shiftL` (8 - n)))

-- | Shift the whole ByteString some number of bits left where 0 <= @n@ < 8
leftShiftByteString :: Int -> L.ByteString -> L.ByteString
leftShiftByteString 0 = id
leftShiftByteString n = snd . L.mapAccumR f 0
    where
        f acc b = (b `shiftR` (8 - n), (b `shiftL` n) .|. acc)

-- | Return a Word8 with the bottom n bits set
bottomNBits :: Int -> Word8
bottomNBits 0 = 0
bottomNBits 1 = 0x01
bottomNBits 2 = 0x03
bottomNBits 3 = 0x07
bottomNBits 4 = 0x0f
bottomNBits 5 = 0x1f
bottomNBits 6 = 0x3f
bottomNBits 7 = 0x7f
bottomNBits 8 = 0xff
bottomNBits x = error ("bottomNBits undefined for " ++ show x)
