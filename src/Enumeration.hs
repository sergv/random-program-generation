{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module Enumeration where

import Control.Applicative hiding (empty)
import Control.Arrow
import qualified Control.Exception as E
import Control.Monad
import Data.List (foldl', tails)
import Data.Tuple (swap)
import Data.Typeable
import System.IO.Unsafe
import System.Random

import Debug.Trace

import IntervalSetList (IntervalSet, Interval(..), mkInterval)
import qualified IntervalSetList as IS

-- import BignumNum
-- import Prelude hiding (product, div, mod, divMod)
--
-- type BigInt = Bignum

import Prelude hiding (product)

type BigInt = Integer


class (Functor f) => Algebraic f where
  empty     :: f a
  singleton :: a -> f a
  -- union must only be applied to disjoint enumerations -
  -- left and right enumerations must have no elements in common.
  union     :: f a -> f a -> f a
  product   :: f a -> f b -> f (a, b)

sum1 :: (Algebraic f) => [f a] -> f a
sum1 []     = empty
sum1 (x:xs) = foldl' union x xs


-- data Fixed a = Fixed
--   { fxCardinality :: BigInt
--   , fxIndex       :: (a -> Bool) -> BigInt -> Result a
--   }
--
-- mkFixed :: BigInt -> ((a -> Bool) -> BigInt -> Result a) -> Fixed a
-- -- mkFixed card _   | trace ("Fixed with cardinality " ++ show card) False = undefined
-- mkFixed card idx = Fixed card idx
--
-- instance Functor Fixed where
--   fmap f fx = fx { fxIndex = g }
--     where
--       g p n =
--         case valid p of
--           Just False -> PredicateFailed [(0, fxCardinality fx)]
--           _          -> fmap f $ fxIndex fx (p . f) n
--           -- Just True  -> fmap f $ fxIndex fx (p . f) n
--           -- Nothing    -> fmap f $ fxIndex fx (p . f) n
--
-- instance Algebraic Fixed where
--   empty = mkFixed 0 (\_ _ -> Error "no elements in empty fixed set")
--   singleton x = mkFixed 1 f
--     where
--       f p 0
--         | p x       = Ok x
--         | otherwise = PredicateFailed [(0, 0)]
--       f _ n = Error $ "cannot get " ++ show n ++ "th index in singleton fixed set"
--   union x y = mkFixed (xCard + fxCardinality y) f
--     where
--       xCard = fxCardinality x
--       f p n | n < xCard = fxIndex x p n
--             | otherwise = fixIndices (+ xCard) $ fxIndex y p $ n - xCard
--   product x y = mkFixed (fxCardinality x * yCard) f
--     where
--       yCard = fxCardinality y
--       f p n = (\x y -> (x, y))
--                 <$> fixIndices (* yCard) (fxIndex x p r)
--                 <*> fixIndices (+ z) (fxIndex y p q)
--         where
--           (r, q) = divMod n yCard
--           z      = r * yCard

data Fixed a where
  Empty      :: Fixed a
  Singleton  :: a -> Fixed a
  Union      :: BigInt -> Fixed a -> Fixed a -> Fixed a
  Product    :: BigInt -> Fixed a -> Fixed b -> Fixed (a, b)
  DotProduct :: BigInt -> [Fixed a] -> [Fixed b] -> Fixed (a, b)
  (:$:)      :: (a -> b) -> Fixed a -> Fixed b -- ^ (a -> b) must be a bijection

ppFx :: Fixed a -> String
ppFx Empty = "Empty"
ppFx (Singleton _) = "Singleton"
ppFx (Union n _ _) = "Union, size = " ++ show n
ppFx (Product n _ _) = "Product, size = " ++ show n
ppFx (DotProduct n _ _) = "DotProduct, size = " ++ show n
ppFx (_ :$: x) = "_ :$: (" ++ ppFx x ++ ")"

fxCardinality :: Fixed a -> BigInt
fxCardinality Empty                 = 0
fxCardinality (Singleton _)         = 1
fxCardinality (Union card _ _)      = card
fxCardinality (Product card _ _)    = card
fxCardinality (DotProduct card _ _) = card
fxCardinality (_ :$: fx)            = fxCardinality fx

infixr 1 :$:

instance Functor Fixed where
  fmap = (:$:)

instance Algebraic Fixed where
  empty       = Empty
  singleton   = Singleton
  union x y   = Union (fxCardinality x + fxCardinality y) x y
  product x y = Product (fxCardinality x * fxCardinality y) x y

instance Applicative Fixed where
  pure = Singleton
  f <*> fx = uncurry ($) :$: (f `product` fx)

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
  --         f n = fxIndex (sum1 $ zipWith product xs rys) n

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
      conv xs rys = DotProduct card xs rys
        where
          card = sum $ zipWith (\x y -> fxCardinality x * fxCardinality y) xs rys
          -- f n = fxIndex (sum1 $ zipWith product xs rys) n

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

fxIndex :: Fixed a -> BigInt -> Either String a
fxIndex Empty _ = Left "no elements in empty fixed set"
fxIndex (Singleton x) 0 = Right x
fxIndex (Singleton _) n = Left $ "cannot get " ++ show n ++ "th index in singleton fixed set"
fxIndex (Union _ x y) n
  | n < xCard = fxIndex x n
  | otherwise = fxIndex y $! n - xCard
  where
    xCard = fxCardinality x
fxIndex (Product _ x y) n = (,) <$> fxIndex x r <*> fxIndex y q
  where
    (r, q) = divMod n $ fxCardinality y
fxIndex (DotProduct _ xs ys) n = fxIndex (sum1 $ zipWith product xs ys) n
fxIndex (f :$: x) n = f <$> fxIndex x n

indexAbs :: forall a. BigInt -> (() -> Enumeration a) -> Either String a
indexAbs n mkEnum = go n 0 (parts $ mkEnum ())
  where
    go :: BigInt -> BigInt -> [Fixed a] -> Either String a
    go _ _ [] = Left "indexAbs: no more parts: index is to large"
    -- go n k _
      -- | trace ("indexAbs: getting " ++ show n ++ " index in fixed set with " ++ show k ++ " constructors") False = undefined
    go n k (fx:fxs)
      | n < fxCardinality fx = fxIndex fx n
      | otherwise            =
        let n' = n - fxCardinality fx
            k' = k + 1
        in  n' `seq` k' `seq` go n' k' fxs

-- Check whether @p@ needs to look at its argument to produce a value.
-- Returns Nothing if it does or (Just b) if its result is b for any input.
--
-- Compared to (const Nothing) implementation with unsafePerformIO
-- makes whole generation program twice as slow.
valid :: (a -> Bool) -> Maybe Bool
valid _p = Nothing
  -- case unsafePerformIO $ E.try $ E.evaluate (p undefined) of
  --   Left (_ :: E.SomeException) -> Nothing
  --   Right x                     -> Just x

data MyException = MyException
  deriving (Typeable, Show)

instance E.Exception MyException

-- TODO: not sure whether this function is useful
inspectsRight :: ((a, b) -> Bool) -> Bool
inspectsRight _p = False
  -- case unsafePerformIO $ E.try $ E.evaluate (p (undefined, E.throw MyException)) of
  --   Left (e :: E.SomeException) ->
  --     case E.fromException e of
  --       Nothing          -> False
  --       Just MyException -> True
  --   Right _                     -> False




data Result a =
    Ok a
  | PredicateFailed [Interval BigInt] -- ^ Ranges of indices for which predicate
                                      -- returned false.
  | Error String
  deriving (Show, Eq, Ord)

mapIndices :: ([Interval BigInt] -> [Interval BigInt]) -> Result a -> Result a
mapIndices _ r@(Ok _)             = r
mapIndices f (PredicateFailed rs) = PredicateFailed $ f rs
mapIndices _ r@(Error _)          = r

instance Functor Result where
  fmap f (Ok x)               = Ok $ f x
  fmap _ (PredicateFailed rs) = PredicateFailed rs
  fmap _ (Error msg)          = Error msg

instance Applicative Result where
  pure = Ok
  Ok f               <*> Ok x                = Ok $ f x
  PredicateFailed rs <*> Ok _                = PredicateFailed rs
  Ok _               <*> PredicateFailed rs' = PredicateFailed rs'
  PredicateFailed rs <*> PredicateFailed rs' = PredicateFailed $ rs ++ rs'
  Error msg          <*> _                   = Error msg
  _                  <*> Error msg'          = Error msg'

dotProduct :: [Fixed a] -> [Fixed b] -> Fixed (a, b)
dotProduct xs ys = sum1 $ zipWith product xs ys


cross :: Fixed a -> Fixed b -> Fixed (a, b)
cross _ Empty                = Empty
cross x (Singleton y)        = (,y) :$: x
cross x (Union _ y z)        = (x `product` y) `union` (x `product` z)
cross x (Product _ y z)      = (\((a, b), c) -> (a, (b, c))) :$: ((x `product` y) `product` z)
cross x (DotProduct _ xs ys) = x `cross` dotProduct xs ys
cross x (f :$: y)            = second f :$: (x `cross` y)

fxIndexPred :: (a -> Bool) -> Fixed a -> BigInt -> Result a
-- fxIndexPred _ fx n | trace ("fxIndexPred n = " ++ show n ++ ", fx = " ++ ppFx fx) False = undefined
fxIndexPred _ Empty _ = Error "no elements in empty fixed set"
-- fxIndexPred _ Empty n = PredicateFailed [mkInterval n n]
fxIndexPred p (Singleton x) 0
  | p x       = Ok x
  | otherwise = PredicateFailed [mkInterval 0 0]
fxIndexPred _ (Singleton _) n = Error $ "cannot get " ++ show n ++ "th index in singleton fixed set"
fxIndexPred p (Union _ x y) n
  | n < xCard =
    fxIndexPred p x n
    -- case fxIndexPred p x n of
    --   res@(Ok _) -> res
    --   -- PredicateFailed _
    --   --   | trace "fxIndexPred: backtracking" False -> undefined
    --   PredicateFailed rs ->
    --     xCard `seq` mapIndices ((++ rs) . map (fmap (+xCard))) $! fxIndexPred p y 0
    --   Error err -> Error err
  | otherwise =
    mapIndices (map (fmap (+xCard))) $! fxIndexPred p y $! n - xCard
  where
    xCard   = fxCardinality x
fxIndexPred p (Product _ x y) n
  | inspectsRight p = fxIndexPred p (swap :$: cross y x) n
  | otherwise       = fxIndexPred p (cross x y) n
fxIndexPred p (DotProduct _ xs ys) n = fxIndexPred p (dotProduct xs ys) n
fxIndexPred p (f :$: x) n =
  case valid p' of
    Just False -> PredicateFailed [mkInterval 0 $ fxCardinality x]
    Just True  -> f <$> fxIndexPred (const True) x n
    Nothing    -> f <$> fxIndexPred p' x n
  where
    p' = p . f

indexPred :: forall a. BigInt -> (a -> Bool) -> (() -> Enumeration a) -> Either String a
indexPred idx pred mkEnum = go idx 0 $ parts $ mkEnum ()
  where
    go :: BigInt -> BigInt -> [Fixed a] -> Either String a
    go _ _ [] = Left "indexPred: no more parts: index is to large"
    -- go n k _
    --   | trace ("indexPred: getting " ++ show n ++ " index in fixed set with " ++ show k ++ " constructors") False = undefined
    go n k fxsOrig@(fx:fxs)
      | n < fxCardinality fx =
        case fxIndexPred pred fx n of
          Ok x               -> Right x
          PredicateFailed rs -> go n' k fxsOrig
            where
              n' = maximum (map (\i -> intervalStart i `max` intervalEnd i) rs) + 1
          Error msg          -> Left msg
      | otherwise =
        let n' = n - fxCardinality fx
            k' = k + 1
        in  n' `seq` k' `seq` go n' k' fxs

generateRandomValues :: forall g a. (RandomGen g) => Fixed a -> (a -> Bool) -> g -> BigInt -> [a]
generateRandomValues fx pred gen tries
  | card /= 0 = {-trace ("cardinality = " ++ show card) $-} go gen IS.empty tries
  | otherwise = error "cannot generate random values from fixed set with cardinality 0"
  where
    card = fxCardinality fx
    badIntervalGrowth = 0 -- card `div` 2^32 -- 1000
    go :: g -> IntervalSet BigInt -> BigInt -> [a]
    -- go _ _ tries
    --  | trace ("#tries = " ++ show tries) False = undefined
    -- go _   badIntervals _
    --   | trace ("|bad intervals| = " ++ show (IS.size badIntervals) ++ ", |excluded elements| = " ++ show (IS.sumIntervals badIntervals)) False = undefined
    go _   _            0     = []
    go gen badIntervals tries =
      tryIdx idx
      -- case IS.lookup idx badIntervals of
      --   Just i  -> tryIdx $ IS.countSucc $ IS.intervalEnd i
      --   Nothing -> tryIdx idx
      where
        (idx, gen') = randomR (0, card) gen
        tries' = tries - 1
        tryIdx :: BigInt -> [a]
        tryIdx n =
          case fxIndexPred pred fx n of
            Ok x               -> x : go gen' badIntervals tries'
            PredicateFailed rs ->
              let (maybeNewItem, n', rs') = growRightEnd n badIntervalGrowth rs
                  -- newIntervals            = IS.insert (mkInterval n n') $ foldr IS.insert badIntervals rs'
                  newIntervals            = badIntervals
              in case maybeNewItem of
                   Just newItem -> newItem : go gen' newIntervals tries'
                   Nothing      -> go gen' newIntervals tries'
            Error _            -> []

    -- @n@ - last tried index that is known to be bad
    growRightEnd :: BigInt -> BigInt -> [Interval BigInt] -> (Maybe a, BigInt, [Interval BigInt])
    growRightEnd n 0 rs = (Nothing, n, rs)
    growRightEnd n k rs =
      case fxIndexPred pred fx n of
        Ok x                -> (Just x, n - 1, rs)
        PredicateFailed rs' -> n' `seq` k' `seq` growRightEnd n' k' (rs' ++ rs)
        Error _             -> (Nothing, n, rs)
      where
        n' = n + 1
        k' = k - 1
