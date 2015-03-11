{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

--module RandomProgramGeneration where

import Control.Applicative hiding (empty)
import qualified Control.Exception as E
import Control.Monad
import Data.List (foldl', tails)
import System.Environment
import System.IO.Unsafe

import Debug.Trace

import BignumNum

import Prelude hiding (product, div, mod, divMod)

type BigInt = Bignum

data Fixed a = Fixed
  { fxCardinality :: BigInt
  , fxIndex       :: BigInt -> Either String a
  }

-- import Prelude hiding (product)
--
-- type BigInt = Integer
--
--
-- data Fixed a = Fixed
--   { fxCardinality :: BigInt
--   , fxIndex       :: BigInt -> Maybe a
--   }


mkFixed :: BigInt -> (BigInt -> Either String a) -> Fixed a
-- mkFixed card _   | trace ("Fixed with cardinality " ++ show card) False = undefined
mkFixed card idx = Fixed card idx

instance Functor Fixed where
  fmap f fx = fx { fxIndex = fmap f . fxIndex fx }

class (Functor f) => Algebraic f where
  empty     :: f a
  singleton :: a -> f a
  -- union must only be applied to disjoint enumerations -
  -- left and right enumerations must have no elements in common.
  union     :: f a -> f a -> f a
  product   :: f a -> f b -> f (a, b)

concat1 :: (Algebraic f) => [f a] -> f a
concat1 []     = empty
concat1 (x:xs) = foldl' union x xs

instance Algebraic Fixed where
  empty = mkFixed 0 (const (Left "no elements in empty fixed set"))
  singleton x = mkFixed 1 f
    where
      f 0 = Right x
      f n = Left $ "cannot get " ++ show n ++ "th index in singleton fixed set"
  union x y = mkFixed (xCard + fxCardinality y) f
    where
      xCard = fxCardinality x
      f n | n < xCard = fxIndex x n
          | otherwise = fxIndex y $ n - xCard
  product x y = mkFixed (fxCardinality x * yCard) f
    where
      yCard = fxCardinality y
      f n = (\x y -> (x, y)) <$> fxIndex x p <*> fxIndex y q
        where
          (p, q) = divMod n yCard

-- lists of parts
-- part - set of values with the given number of constructors
newtype Enumeration a = Enumeration { parts :: [Fixed a] }

pay :: Enumeration a -> Enumeration a
pay (Enumeration ps) = Enumeration $ empty : ps

instance Functor Enumeration where
  fmap f (Enumeration xs) = Enumeration $ map (fmap f) xs

instance Algebraic Enumeration where
  empty = Enumeration []
  singleton x = Enumeration [singleton x]
  union (Enumeration xs) (Enumeration ys) = Enumeration $ zipPlus xs ys
    where
      zipPlus []     ys     = ys
      zipPlus xs     []     = xs
      zipPlus (x:xs) (y:ys) = union x y : zipPlus xs ys
  -- product :: forall a b. Enumeration a -> Enumeration b -> Enumeration (a, b)
  -- product (Enumeration xs) (Enumeration ys) =
  --   Enumeration $ prod' xs $ reversals ys
  --   where
  --     prod' xs@(_:xs') (ys:yss) = goY ys yss
  --       where
  --         goY ry rys = conv xs ry : case rys of
  --                                     []       -> goX ry xs'
  --                                     ry':rys' -> goY ry' rys'
  --         goX ry = map (`conv` ry) . tails
  --     prod' _ _ = []
  --     conv :: [Fixed a] -> [Fixed b] -> Fixed (a, b)
  --     conv xs rys = mkFixed card f
  --       where
  --         card = sum $ zipWith (\x y -> fxCardinality x * fxCardinality y) xs rys
  --         f n = fxIndex (concat1 $ zipWith product xs rys) n

  product :: forall a b. Enumeration a -> Enumeration b -> Enumeration (a, b)
  product (Enumeration xs) (Enumeration ys) = Enumeration $
    -- map (conv xs) $ reversals ys
    prod xs $ reversals ys
    where
      prod :: [Fixed a] -> [[Fixed b]] -> [Fixed (a, b)]
      prod xs@(_:xs') (ys:yss) = go ys yss
        where
          go :: [Fixed b] -> [[Fixed b]] -> [Fixed (a, b)]
          go ry rys = conv xs ry : rest
            where
              rest = case rys of
                       []       ->
                         -- Corresponds to padding ry with empties, but multiplying
                         -- by empty is the same as dropping that element. Thus
                         -- ry is semantically padded with emties which cause
                         -- prefixes of xs' to be dropped.
                         -- NB Use xs' instead of xs because xs was already used
                         -- in conjunction with ry in the go function.
                         map (`conv` ry) $ tails xs'
                       ry':rys' -> go ry' rys'
      prod _ _ = []
      conv :: [Fixed a] -> [Fixed b] -> Fixed (a, b)
      conv xs rys = mkFixed card f
        where
          card = sum $ zipWith (\x y -> fxCardinality x * fxCardinality y) xs rys
          f n = fxIndex (concat1 $ zipWith product xs rys) n

instance Applicative Enumeration where
  pure = singleton
  fs <*> xs = uncurry ($) <$> (fs `product` xs)

reversals :: [a] -> [[a]]
reversals xs = go [] xs
  where
    go _  []     = []
    go rs (x:xs) = rs' : go rs' xs
      where
        rs' = x : rs


enumerateBool :: Enumeration Bool
enumerateBool = pay $ singleton True `union` singleton False

enumerateList :: Enumeration a -> Enumeration [a]
-- enumerateList x = pay $ singleton [] `union` ((:) <$> x <*> enumerateList x)
enumerateList x = enum
  where
    enum = pay $ singleton [] `union` ((:) <$> x <*> enum)

boolLists :: () -> Enumeration [Bool]
boolLists () = enumerateList enumerateBool

indexAbs :: BigInt -> (() -> Enumeration a) -> Either String a
indexAbs n mkEnum = go n 0 (parts $ mkEnum ())
  where
    go _ _ [] = Left "indexAbs: no more parts: index is to large"
    go n k _
      | trace ("getting " ++ show n ++ " index in fixed set with " ++ show k ++ " constructors") False = undefined
    go n k (x:xs)
      | n < fxCardinality x = fxIndex x n
      | otherwise           =
        let n' = n - fxCardinality x
            k' = k + 1
        in  n' `seq` k' `seq` go n' k' xs

-- Check whether @p@ needs to look at its argument to produce a value.
-- Returns Nothing if it does or (Just b) if its result is b for any input.
valid :: (a -> Bool) -> Maybe Bool
valid p =
  case unsafePerformIO $ E.try $ E.evaluate (p undefined) of
    Left (_ :: E.SomeException) -> Nothing
    Right x                     -> Just x



main :: IO ()
main = do
  args <- getArgs
  case args of
    [n]    -> putStrLn $ show $ indexAbs (read n) boolLists
    [p, q] -> putStrLn $ show $ indexAbs (read p ^ read q) boolLists
