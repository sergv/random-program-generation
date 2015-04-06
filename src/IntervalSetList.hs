{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ScopedTypeVariables      #-}

module IntervalSetList
  ( Interval
  , mkInterval
  , intervalStart
  , intervalEnd
  , IntervalSet
  , isInside
  , empty
  , size
  , sumIntervals
  , null
  , union
  , insert
  , lookup
  , Countable(..)
  )
where

import Control.Applicative hiding (empty)
--import Data.Function
import qualified Data.List as L
import Prelude hiding (null, lookup)

import Data.Maybe
import Data.Proxy (Proxy(..))
import Test.QuickCheck


data Interval a = Interval
  { intervalStart :: a
  , intervalEnd   :: a
  }
  deriving (Functor)
  -- deriving (Show) --, Eq, Ord)

instance (Show a) => Show (Interval a) where
  show (Interval x y) = "(" ++ show x ++ ", " ++ show y ++ ")"

mkInterval :: (Ord a) => a -> a -> Interval a
mkInterval x y
  | x < y     = Interval x y
  | otherwise = Interval y x

instance (Eq a) => Eq (Interval a) where
  (==) (Interval xl _) (Interval yl _) = xl == yl

instance (Ord a) => Ord (Interval a) where
  compare (Interval xl _) (Interval yl _) = xl `compare` yl

isInside :: (Ord a) => a -> Interval a -> Bool
isInside x (Interval left right) = left <= x && x <= right

isIntersect :: (Ord a) => Interval a -> Interval a -> Bool
isIntersect (Interval xl xr) y =
  isInside xl y || isInside xr y

class Countable a where
  countSucc :: a -> a
--  countPrev :: a -> Maybe a

instance Countable Integer where
  countSucc = (+1)
--  countPrev n
--    | n <= 0    = Nothing
--    | otherwise = Just $ n - 1

isMergeable :: (Ord a, Countable a) => Interval a -> Interval a -> Bool
isMergeable x@(Interval xl xr) y@(Interval yl yr) =
  isIntersect x y ||
  -- x is to the left of y
  countSucc xr == yl ||
  -- y is to the left of x
  countSucc yr == xl

merge :: (Ord a, Countable a) => Interval a -> Interval a -> Interval a
merge x@(Interval xl xr) y@(Interval yl yr)
  | isMergeable x y =
    Interval (xl `min` yl) (xr `max` yr)
  | otherwise       =
    error "merge Should not merge disjoint intervals"

-- Intervals are sorted my their first element.
-- There're no overlapping intervals => all interval starts are unique.
-- For every interval, start (left) is <= end (right).
newtype IntervalSet a = IntervalSet { intervals :: [Interval a] }
  deriving (Show, Eq, Ord)

empty :: IntervalSet a
empty = IntervalSet []

size :: IntervalSet a -> Integer
size (IntervalSet xs) = L.genericLength xs

sumIntervals :: (Num a) => IntervalSet a -> a
sumIntervals (IntervalSet xs) =
  sum $ map (\x -> 1 + intervalEnd x - intervalStart x) xs

null :: IntervalSet a -> Bool
null = L.null . intervals

lookup :: (Ord a) => a -> IntervalSet a -> Maybe (Interval a)
lookup x (IntervalSet ys) = go ys
  where
    go [] = Nothing
    go (y:ys)
      | isInside x y = Just y
      | otherwise    = go ys

insert :: (Ord a, Countable a) => Interval a -> IntervalSet a -> IntervalSet a
insert x (IntervalSet ys) = IntervalSet $ go x ys
  where
    go x [] = [x]
    go x@(Interval xl _) ys'@(y@(Interval yl _):ys)
      | isMergeable x y = go (x `merge` y) ys
      | xl > yl         = y : go x ys
      | otherwise       = x : ys'

union :: forall a. (Ord a, Countable a) => IntervalSet a -> IntervalSet a -> IntervalSet a
union (IntervalSet xs) (IntervalSet ys) = IntervalSet $ go xs ys
  where
    go :: [Interval a] -> [Interval a] -> [Interval a]
    go []     ys     = ys
    go xs     []     = xs
    go (x:xs) (y:ys)
      | isMergeable x y = merge x y : go xs ys
      | x < y           = x : go xs (y : ys)
      | otherwise       = y : go (x : xs) ys

_insert' :: (Integer, Integer) -> IntervalSet Integer -> IntervalSet Integer
_insert' (x, y) = insert (Interval x y)

-- Testing

newtype NaturalInteger = NaturalInteger Integer
  deriving (Eq, Ord)

instance Show NaturalInteger where
  show (NaturalInteger x) = show x

instance Countable NaturalInteger where
  countSucc (NaturalInteger x) = NaturalInteger $ countSucc x

instance Arbitrary NaturalInteger where
  arbitrary =
    (\n -> NaturalInteger $ if n > 0 then 2 * n + 1 else 2 * negate n) <$> arbitrary
  shrink (NaturalInteger n)
    | n > 0     = [NaturalInteger $! n - 1]
    | otherwise = []

instance (Arbitrary a, Ord a) => Arbitrary (Interval a) where
  arbitrary = mkInterval <$> arbitrary <*> arbitrary
  shrink (Interval x y) =
    [ mkInterval x' y'
    | x' <- shrink x
    , y' <- shrink y
    ]

data IntervalSetListTest a = IntervalSetListTest [Interval a] (IntervalSet a)

instance (Show a) => Show (IntervalSetListTest a) where
  show (IntervalSetListTest xs _) = show xs

instance (Arbitrary a, Ord a, Countable a) => Arbitrary (IntervalSetListTest a) where
  arbitrary = do
    xs <- listOf arbitrary
    return $ IntervalSetListTest xs $ foldr insert empty xs
  shrink (IntervalSetListTest xs _) =
    map (\ys -> IntervalSetListTest ys $ foldr insert empty ys) $ shrink xs

prop_IntervalSetList_Ordered :: (Ord a, Countable a) => IntervalSetListTest a -> Bool
prop_IntervalSetList_Ordered (IntervalSetListTest _ (IntervalSet ys)) =
  isOrdered ys

isOrdered :: (Ord a) => [a] -> Bool
isOrdered xs = and $ zipWith (<=) xs $ drop 1 xs

prop_IntervalSetList_NoIntersections :: (Ord a, Countable a) => IntervalSetListTest a -> Bool
prop_IntervalSetList_NoIntersections (IntervalSetListTest _ (IntervalSet ys)) =
  and (zipWith (\y y' -> not $ isIntersect y y') ys $ drop 1 ys)

prop_IntervalSetList_NoIntervalsNextToEachOther :: (Ord a, Countable a) => IntervalSetListTest a -> Bool
prop_IntervalSetList_NoIntervalsNextToEachOther (IntervalSetListTest _ (IntervalSet ys)) =
  and (zipWith (\y y' -> countSucc (intervalEnd y) /= intervalStart y') ys $ drop 1 ys)

prop_IntervalSetList_AllElementsPresent :: (Ord a, Countable a) => IntervalSetListTest a -> Bool
prop_IntervalSetList_AllElementsPresent (IntervalSetListTest xs set) =
  all (\elem -> isJust $ lookup elem set) elements
  where
    elements = concatMap intervalElements xs

intervalElements :: forall a. (Ord a, Countable a) => Interval a -> [a]
intervalElements (Interval start end) = go start
  where
    go :: a -> [a]
    go x | x == end  = [x]
         | otherwise = x : go (countSucc x)

prop_IntervalSetList :: forall a. (Arbitrary a, Show a, Ord a, Countable a) => Proxy a -> Property
prop_IntervalSetList _ =
  (prop_IntervalSetList_Ordered :: IntervalSetListTest a -> Bool) .&&.
  (prop_IntervalSetList_NoIntersections :: IntervalSetListTest a -> Bool) .&&.
  (prop_IntervalSetList_NoIntervalsNextToEachOther :: IntervalSetListTest a -> Bool) .&&.
  (prop_IntervalSetList_AllElementsPresent :: IntervalSetListTest a -> Bool)

test :: IO ()
test =
  quickCheckWith
    (stdArgs { maxSuccess = 1000000, maxSize = 1000000 })
    (prop_IntervalSetList naturalIntegerProxy)

naturalIntegerProxy :: Proxy NaturalInteger
naturalIntegerProxy = Proxy

