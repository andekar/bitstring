-- Copyright (c) A Karlsson 2010 
-- Copyright (c) T Olausson 2010
module Data.Binary.BitString.Tests where

import Data.Binary.BitString.BitString

import Prelude hiding (null,head,tail,take,drop,concat,splitAt, length)
import Data.Word
import Control.Monad (liftM)
import Control.Arrow (first,second)
import qualified Data.List as List
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Internal as LI
import Test.QuickCheck
import Data.Bits

instance Arbitrary Word8 where
    arbitrary = do 
        i <- choose (0,255) :: Gen Int
        return $ fromIntegral i
    shrink i = map fromInteger $ shrink (toInteger i)

instance Arbitrary BitString where
    arbitrary = sized $ \n -> choose (0,n) >>= myArbitrary where 
        myArbitrary :: Int -> Gen BitString
        myArbitrary 0 = return Empty
        myArbitrary n = do
            chunk <- arbitrary
            rest  <- myArbitrary (n-1)
            begin <- liftM fromIntegral (choose (0,7) :: Gen Int)
            end   <- liftM fromIntegral (choose (0,7) :: Gen Int)
            return $ Chunk chunk begin end rest
    
    shrink Empty = []
    shrink (Chunk lb begin end rest) = 
        [rest] ++
        [(Chunk i begin end rest) | i <- shrink lb   ] ++
        [(Chunk lb i end rest)    | i <- shrink begin] ++
        [(Chunk lb begin i rest)  | i <- shrink end  ] ++
        [(Chunk lb begin end i)   | i <- shrink rest ]

instance Arbitrary L.ByteString where
    arbitrary = sized $ \n -> choose (0,n) >>= myArbitrary where 
        myArbitrary :: Int -> Gen L.ByteString
        myArbitrary 0 = return LI.Empty
        myArbitrary n = do
            ws  <- arbitrary
            return $ L.pack ws

    shrink = map L.pack . shrink . L.unpack

prop_invariant :: BitString -> Bool
prop_invariant Empty = True
prop_invariant (Chunk lb begin end rest)
    | begin + end >= 8 && L.length lb == 1 = False
    | begin > 7 = False
    | end > 7 = False
    | L.null lb                          = False
    | otherwise                          = prop_invariant rest

prop_take :: Int -> BitString -> Property
prop_take i bis = prop_invariant bis ==> 
        List.take i' bList == bisToList (take (fromIntegral i') bis)
      && prop_invariant (take (fromIntegral i') bis)
    where
        bList = bisToList bis
        i' = fromIntegral $ abs i

-- this is broken
prop_takeWord8 :: BitString -> Property
prop_takeWord8 bis = (prop_invariant bis && length bis >= 8 ) ==>
                    List.take 8 bList
                  == bisToList (Chunk (L.pack [takeWord8 bis]) 0 0 Empty)
    where bList = bisToList bis

-- Now this one is correctly defined
-- However consider this case:
-- bis = Chunk (Chunk "\STX" Empty) 5 1 Empty
-- i   = 3
-- That makes the property fail
-- TODO: This needs to be checked in takeAsWord8 
prop_takeAsWord8 :: Int -> BitString -> Property
prop_takeAsWord8 i bis =
    -- Lots of conditions here...
    prop_invariant bis && i > 0 ==>
        (fst $ foldr (\b (acc,v) -> if b == 1 
                                    then (acc + v,v*2) 
                                    else (acc,v*2)) (0,1) (List.take i' $ bisToList $ bis))
        == takeAsWord8 i' bis
  where
    i' = i `mod` 8
                          

prop_drop :: Int -> BitString -> Property
prop_drop i bis = prop_invariant bis ==>
                  List.drop (fromIntegral i') (bisToList bis)
                == bisToList fun
                && prop_invariant fun
    where i' = abs $ fromIntegral i
          fun = (drop i' bis)

prop_splitAt :: Int -> BitString -> Property
prop_splitAt i bis = prop_invariant bis ==>
                      List.splitAt (fromIntegral i') (bisToList bis)
                   == lr bisToList
                   && tr (lr prop_invariant)
    where i' = abs $ fromIntegral i
          lr f= second f (first f (splitAt i' bis))
          tr (True,True) = True
          tr _  = False

prop_head :: BitString -> Property
prop_head Empty = True ==> True
prop_head bis = prop_invariant bis ==>
                List.head (bisToList bis) == if (head bis) then 1 else 0

prop_tail :: BitString -> Property
prop_tail bis = (prop_invariant bis && length bis > 0) ==>
                List.tail (bisToList bis) == bisToList (tail bis)
              && prop_invariant (tail bis)

prop_append :: BitString -> BitString -> Property
prop_append bis bis' = prop_invariant bis && prop_invariant bis' ==>
                        (f bis) ++ (f bis')
                     ==  f fun
                     &&  prop_invariant fun
    where f = bisToList
          fun = append bis bis'

prop_concat :: [BitString] -> Property
prop_concat biss = and (map prop_invariant biss) ==>
                   List.concat (map f biss)
                 == f (concat biss)
                 && prop_invariant (concat biss)
    where f = bisToList

prop_length :: BitString -> Property
prop_length bs = prop_invariant bs ==> 
                 List.length (bisToList bs) == (fromIntegral $ length bs)

prop_atLeast :: Int -> BitString -> Property
prop_atLeast i bs = prop_invariant bs && i >= 0 ==>
                    (List.length (bisToList bs) >= (fromIntegral i))
                        == atLeast bs (fromIntegral i)

prop_atLeastBS :: Int -> L.ByteString -> Property
prop_atLeastBS i bs = i >= 0 ==>
                      ((L.length bs * 8) >= (fromIntegral i))
                    == atLeastBS bs (fromIntegral i)

bisToList :: BitString -> [Int]
bisToList bs = nums
  where 
    nums = btl bs
    btl :: BitString -> [Int]
    btl Empty = []
    btl (Chunk lb begin end rest)
        | L.null lb = bisToList rest
        | begin+end == 8 && L.length lb == 1 = bisToList rest
        | begin == 7 = f bit : (bisToList $ Chunk (L.tail lb) 0 end rest)
        | otherwise  = f bit : (bisToList $ Chunk lb (begin + 1) end rest)
      where
        bit = testBit (L.head lb) (7 - fi begin)
        f True  = 1
        f False = 0

-- Recursive splitAt, no need for it here though...
splitAtMany :: Int -> [a] -> [[a]]
splitAtMany _ [] = []
splitAtMany i xs = f : splitAtMany i b
  where
    (f,b) = List.splitAt i xs

-- Shorthand for testing 500 times
largeTest :: (Testable prop) => prop -> IO ()
largeTest prop = quickCheckWith (stdArgs { maxSuccess = 500, maxDiscard = 10000 }) prop
