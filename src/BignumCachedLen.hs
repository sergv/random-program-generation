module Bignum where

import Data.Char
import Data.List
import Text.Printf
--import Text.Read

import Prelude hiding (divMod, div, mod)
import qualified Prelude as P

import Debug.Trace

data Bit = Zero | One
  deriving (Show, Eq, Ord, Enum, Bounded)


-- bits stored in least significant first - li.e. ittle endian - order
data Bignum = Bignum
  { getBits :: [Bit]
  , bitsLen :: Int
  }

instance Show Bignum where
  show (Bignum xs _) = "0b" ++ map bit (reverse xs) -- ++ "/0d" ++ show (toNat x)
    where
      bit :: Bit -> Char
      bit Zero = '0'
      bit One  = '1'

instance Read Bignum where
  readsPrec _ xs = [(readBignum ys, xs')]
    where
      (ys, xs') = span (\c -> '0' <= c && c <= '9') xs

readBignum :: String -> Bignum
readBignum =
  snd .
  foldr (\x (b, y) -> (b .*. ten, b .*. x .+. y)) (one, zero) .
  map digitVal
  where
    digitVal c = fromNat $ fromIntegral $ ord c - ord '0'
    ten        = fromNat 10

zero :: Bignum
zero = Bignum [] 0

one :: Bignum
one = Bignum [One] 1

isZero :: Bignum -> Bool
isZero (Bignum xs _) = all (== Zero) xs

normalize :: Bignum -> Bignum
normalize (Bignum xs _) = Bignum bits (length bits)
  where
    bits = reverse xs'
    xs' = case dropWhile (== Zero) $ reverse xs of
            [] -> [Zero]
            ys -> ys

(.+.) :: Bignum -> Bignum -> Bignum
(.+.) (Bignum xs _) (Bignum ys _) = Bignum bits (length bits)
  where
    bits = addBits xs ys

addBits :: [Bit] -> [Bit] -> [Bit]
-- addBits xs ys | trace ("+: |xs| = " ++ show (length xs) ++ ", |ys| = " ++ show (length ys)) False = undefined
addBits [] ys = ys
addBits xs [] = xs
addBits xs ys = go Zero xs ys
  where
    go :: Bit -> [Bit] -> [Bit] -> [Bit]
    go carry []       []        =
      case carry of
        Zero -> []
        One  -> [One]
    go carry []       (y:ys)    = y : go carry [] ys
    go carry (x:xs)   []        = x : go carry xs []
    go Zero (Zero:xs) (Zero:ys) = Zero : go Zero xs ys
    go Zero (Zero:xs) (One:ys)  = One  : go Zero xs ys
    go Zero (One:xs)  (Zero:ys) = One  : go Zero xs ys
    go Zero (One:xs)  (One:ys)  = Zero : go One xs ys
    go One  (Zero:xs) (Zero:ys) = One  : go Zero xs ys
    go One  (Zero:xs) (One:ys)  = Zero : go One xs ys
    go One  (One:xs)  (Zero:ys) = Zero : go One xs ys
    go One  (One:xs)  (One:ys)  = One  : go One xs ys

{-# INLINE zipPad #-}
-- | zip lists of bits and pad with zeroes to the length of the longest one
zipPad :: [Bit] -> [Bit] -> [(Bit, Bit)]
zipPad []     []     = []
zipPad (x:xs) []     = (x, Zero): zipPad xs []
zipPad []     (y:ys) = (Zero, y): zipPad [] ys
zipPad (x:xs) (y:ys) = (x, y): zipPad xs ys

-- addBits :: [Bit] -> [Bit] -> [Bit]
-- addBits xs ys =
--   case foldl' go ([], Zero) $ zipPad xs ys of
--     (zs, Zero) -> reverse zs
--     (zs, One)  -> reverse $ One : zs
--   where
--     go :: ([Bit], Bit) -> (Bit, Bit) -> ([Bit], Bit)
--     go (zs, carry) (x, y) = (z:zs, carry')
--       where
--         (z, carry') = add x y carry
--     add :: Bit -> Bit -> Bit -> (Bit, Bit)
--     add Zero Zero Zero = (Zero, Zero)
--     add Zero Zero One  = (One, Zero)
--     add Zero One  Zero = (One, Zero)
--     add Zero One  One  = (Zero, One)
--     add One  Zero Zero = (One, Zero)
--     add One  Zero One  = (Zero, One)
--     add One  One  Zero = (Zero, One)
--     add One  One  One  = (One, One)

toNat :: Bignum -> Integer
toNat (Bignum xs _) =
  foldl' (\acc (k, b) -> acc + bit b * (2^k)) 0 $ zip [0..] xs
  where
    bit :: Bit -> Integer
    bit Zero = 0
    bit One  = 1

fromNat :: Integer -> Bignum
fromNat n = Bignum bits (length bits)
  where
    bits = go n
    go :: Integer -> [Bit]
    go 0 = [Zero]
    go 1 = [One]
    go n | m == 0    = Zero: go n'
         | otherwise = One: go n'
      where
        (n', m) = P.divMod n 2

multBy2 :: Bignum -> Bignum
multBy2 (Bignum xs len) = Bignum (mulBitsBy2 xs) (len + 1)

mulBitsBy2 :: [Bit] -> [Bit]
mulBitsBy2 = (Zero:)

(.*.) :: Bignum -> Bignum -> Bignum
(.*.) = mulSlow

mulSlow :: Bignum -> Bignum -> Bignum
mulSlow (Bignum xs xsLen) (Bignum ys ysLen) = Bignum bits (length bits)
  where
    bits = mulBitsSlow xs xsLen ys ysLen

mulBitsSlow :: [Bit] -> Int -> [Bit] -> Int -> [Bit]
-- mulBitsSlow xs ys | trace ("*: |xs| = " ++ show (length xs) ++ ", |ys| = " ++ show (length ys)) False = undefined
mulBitsSlow xs xsLen ys ysLen
  | xsLen < ysLen = go ys xs []
  | otherwise     = go xs ys []
  where
    go :: [Bit] -> [Bit] -> [Bit] -> [Bit]
    go _ []         acc = acc
    go x (Zero: ys) acc = go (mulBitsBy2 x) ys acc
    go x (One: ys)  acc = go (mulBitsBy2 x) ys $! acc `addBits` x

(.<.) :: Bignum -> Bignum -> Bool
(.<.) (Bignum xs _) (Bignum ys _) =
  foldr (\(x, y) acc -> x < y || x == y && acc) False $
  reverse $
  zipPad xs ys

(.<=.) :: Bignum -> Bignum -> Bool
(.<=.) x y = x .==. y ||  x .<. y

(.==.) :: Bignum -> Bignum -> Bool
(.==.) (Bignum xs _) (Bignum ys _) =
  all (uncurry (==)) $ zipPad xs ys

(./=.) :: Bignum -> Bignum -> Bool
(./=.) x y = not $ x .==. y

instance Eq Bignum where
  (==) = (.==.)

instance Ord Bignum where
  compare x y
    | x .<. y   = LT
    | x .==. y  = EQ
    | otherwise = GT

-- | Second argument
(.-.) :: Bignum -> Bignum -> Bignum
(.-.) x@(Bignum xs _) y@(Bignum ys _) =
  case foldl' go ([], Zero) $ zipPad xs ys of
    (zs, Zero) ->
      Bignum (reverse zs) (length zs)
    (_, One)   ->
      error $ printf "Trying to subtract bigger number from the smaller one: %s - %s" (show x) (show y)
  where
    go :: ([Bit], Bit) -> (Bit, Bit) -> ([Bit], Bit)
    go (zs, carry) (x, y) = (z:zs, carry')
      where
        (z, carry') = subBits x y carry
    subBits :: Bit -> Bit -> Bit -> (Bit, Bit)
    subBits Zero Zero Zero = (Zero, Zero)
    subBits Zero Zero One  = (One, One)
    subBits Zero One  Zero = (One, One)
    subBits Zero One  One  = (Zero, One)
    subBits One  Zero Zero = (One, Zero)
    subBits One  Zero One  = (Zero, Zero)
    subBits One  One  Zero = (Zero, Zero)
    subBits One  One  One  = (One, One)

div :: Bignum -> Bignum -> Bignum
div x y = fst $ divMod x y

mod :: Bignum -> Bignum -> Bignum
mod x y = snd $ divMod x y

-- for x and y numbers return pair (q, r) such that x = q * y + r, r < y
divMod :: Bignum -> Bignum -> (Bignum, Bignum)
divMod x@(Bignum xs _) y
  | isZero y  = error $ "Cannot divide " ++ show x ++ " by 0"
  | otherwise = go xs
  where
    go :: [Bit] -> (Bignum, Bignum)
    go []      = (Bignum [] 0, Bignum [] 0)
    go (b: xs)
      | r' .<. y  = (q', r')
      | otherwise = (q' .+. one, r' .-. y)
      where
        (Bignum qs qsLen, Bignum rs rsLen) = go xs
        qs' = Zero: qs
        rs' = b: rs
        q'  = Bignum qs' (qsLen + 1)
        r'  = Bignum rs' (rsLen + 1)

gcdEuclid :: Bignum -> Bignum -> Bignum
gcdEuclid x y
  | y .==. zero = x
  | otherwise   = gcdEuclid y (x `mod` y)
