----------------------------------------------------------------------------
-- |
-- Module      :  RandomProgramGenerationGADT
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}

module RandomProgramGenerationGADT where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Exception as E
import Data.Tuple
import Data.Typeable (Typeable)
import System.IO
import System.IO.Unsafe
import System.Random

--import Debug.Trace

newtype HFix f ix = HFix { unHFix :: f (HFix f ix) ix }

-- Space of values of type a
data Space a where
  Empty :: Space a
  Pure  :: a        -> Space a
  (:+:) :: Space a  -> Space a -> Space a
  (:*:) :: Space a  -> Space b -> Space (a, b)
  Pay   :: Space a  -> Space a
  (:$:) :: (a -> b) -> Space a -> Space b

instance Show (Space a) where
  showsPrec _ Empty = showString "Empty"
  showsPrec p (Pure _) = showParen (p >= 10) $ showString "Pure _"
  showsPrec p (_ :+: _) =
    showParen (p >= 10) $ showString "_ :+: _"
  showsPrec p (_ :*: _) =
    showParen (p >= 10) $ showString "_ :*: _"
  showsPrec p (Pay _) = showParen (p >= 10) $ showString "Pay _"
  showsPrec p (_ :$: _) =
    showParen (p >= 10) $ showString "_ :$: _"

infixr 1 :$:
infixr 6 :+:
infixr 7 :*:

instance Functor Space where
  --fmap :: (a -> b) -> Space a -> Space b
  fmap _ Empty       = Empty
  fmap f (Pure x)    = Pure $ f x
  fmap f (s :+: s')  = fmap f s :+: fmap f s'
  fmap f p@(_ :*: _) = f :$: p -- does not preserve functor law fmap id == id
  fmap f (Pay s)     = Pay $ fmap f s
  fmap f (g :$: s)   = f . g :$: s

--instance Applicative Space where
--  pure = Pure
--  (<*>) sf sx = (\(f, x) -> f x) :$: sf :*: sx

infix 5 ^$^
infixr 4 ^*^

(^$^) :: (a -> b) -> Space a -> Space b
(^$^) = (:$:)

(^*^) :: Space (a -> b) -> Space a -> Space b
(^*^) sf sx = (\(f, x) -> f x) :$: sf :*: sx

data Nat =
    Zero
  | Succ Nat
  deriving (Show, Eq, Ord)

natSpace :: () -> Space Nat
natSpace _ = space
  where
    space = Pay $ Pure Zero :+: (Succ ^$^ space)

listSpace :: Space a -> Space [a]
listSpace elemSpace = space
  where
    space = Pay $ Pure [] :+: ((:) ^$^ elemSpace ^*^ space)

isListSorted :: (Ord a) => [a] -> Bool
isListSorted []             = True
isListSorted [_]            = True
isListSorted (x1:xs@(x2:_)) = x1 <= x2 && isListSorted xs

data ValueSet a where
  EmptySet  :: ValueSet a
  Singleton :: a -> ValueSet a
  Union     :: Integer -> ValueSet a -> ValueSet a -> ValueSet a
  Product   :: Integer -> ValueSet a -> ValueSet b -> ValueSet (a, b)
  FMap      :: (a -> b) -> ValueSet a -> ValueSet b

instance Show (ValueSet a) where
  showsPrec _ EmptySet = showString "EmptySet"
  showsPrec p (Singleton _) =
    showParen (p >= 10) $ showString "Singleton" . showChar ' ' . showChar '_'
  showsPrec p (Union _ s s') =
    showParen (p >= 10) $
    showString "Union" . showChar ' ' .
    showsPrec 11 s . showChar ' ' .
    showsPrec 11 s'
  showsPrec p (Product _ s s') =
    showParen (p >= 10) $
    showString "Product" . showChar ' ' .
    showsPrec 11 s . showChar ' ' .
    showsPrec 11 s'
  showsPrec p (FMap _ s) =
    showParen (p >= 10) $
    showString "FMap" . showChar ' ' . showChar '_' . showChar ' ' . showsPrec 11 s

instance Functor ValueSet where
  fmap _ EmptySet          = EmptySet
  fmap f (Singleton x)     = Singleton $ f x
  fmap f (Union k s s')    = Union k (fmap f s) (fmap f s')
  fmap f p@(Product _ _ _) = FMap f p
  fmap f (FMap g s)        = FMap (f . g) s

valueSetSize :: ValueSet a -> Integer
valueSetSize EmptySet        = 0
valueSetSize (Singleton _)   = 1
valueSetSize (Union k _ _)   = k
valueSetSize (Product k _ _) = k
valueSetSize (FMap _ s)      = valueSetSize s

mkUnion :: ValueSet a -> ValueSet a -> ValueSet a
mkUnion EmptySet y        = y
mkUnion x        EmptySet = x
mkUnion x        y        = Union size x y
  where
    size = valueSetSize x + valueSetSize y

mkProduct :: ValueSet a -> ValueSet b -> ValueSet (a, b)
mkProduct EmptySet      _             = EmptySet
mkProduct _             EmptySet      = EmptySet
mkProduct (Singleton x) y             = FMap (\y -> (x, y)) y
mkProduct x             (Singleton y) = FMap (\x -> (x, y)) x
mkProduct x             y             = Product size x y
  where
    size = valueSetSize x * valueSetSize y

indexFin :: ValueSet a -> Integer -> a
indexFin EmptySet      _ = error "cannot index into empty set"
indexFin (Singleton x) 0 = x
indexFin (Singleton _) _ = error "cannot take nonzero index out of singleton set"
indexFin (Union _ v v') k
  | k < valueSetSize v = indexFin v k
  | otherwise          = indexFin v' $ k - valueSetSize v
indexFin (Product _ v v') k = (indexFin v k1, indexFin v' k2)
  where
    (k1, k2) = divMod k (valueSetSize v') -- valueSetSize v
indexFin (FMap f v) k = f $ indexFin v k

sizedSet :: Integer -> Space a -> ValueSet a
-- sizedSet k s | trace ("k = " ++ show k ++ ", s = " ++ show s) False = undefined
sizedSet _ Empty      = EmptySet
sizedSet 0 (Pure x)   = Singleton x
sizedSet _ (Pure _)   = EmptySet
sizedSet 0 (Pay _)    = EmptySet
sizedSet k (s :+: s') = sizedSet k s `mkUnion` sizedSet k s'
sizedSet k (s :*: s') =
  foldr1 mkUnion $
  [ sizedSet n s `mkProduct` sizedSet (k - n) s' | n <- [0..k] ]

  -- map (\(k1, k2) -> sizedSet k1 s `mkProduct` sizedSet k2 s') $
  -- possibleSums k
sizedSet k (Pay s)    = sizedSet (k - 1) s
sizedSet k (f :$: s)  = FMap f $ sizedSet k s

{-# INLINE possibleSums #-}
-- | Decompose @k@ into pairs (k1, k2) such that
-- k1 > 0, k2 > 0, k1 + k2 = k.
possibleSums :: Integer -> [(Integer, Integer)]
possibleSums 0 = []
possibleSums k = [ (n, k - n) | n <- [0..k] ]

reifyValues :: ValueSet a -> [a]
reifyValues s = go s []
  where
    go :: ValueSet a -> [a] -> [a]
    go EmptySet         acc = acc
    go (Singleton x)    acc = x:acc
    go (Union _ s s')   acc = go s $ go s' acc
    go (Product _ s s') acc =
      [ (x, y) | x <- go s [], y <- go s' [] ] `zipEven` acc
    go (FMap f s)       acc = map f (go s []) `zipEven` acc

zipEven :: [a] -> [a] -> [a]
zipEven []     ys     = ys
zipEven xs     []     = xs
zipEven (x:xs) (y:ys) = x: y: zipEven xs ys

-- Indexing with a predicate

-- Check whether @p@ needs to look at its argument to produce a value.
-- Returns Nothing if it does or (Just b) if its result is b for any input.
valid :: (a -> Bool) -> Maybe Bool
valid p =
  case unsafePerformIO $ E.try $ E.evaluate (p undefined) of
    Left (_ :: E.SomeException) -> Nothing
    Right x                     -> Just x

-- derive separate exception instances here

data MyException = MyException
  deriving (Typeable, Show)

instance Exception MyException

inspectsRight :: ((a, b) -> Bool) -> Bool
inspectsRight p =
  case unsafePerformIO $ E.try $ E.evaluate (p (undefined, throw MyException)) of
    Left (e :: E.SomeException) ->
      case fromException e of
        Nothing          -> False
        Just MyException -> True
    Right _                     -> False

-- -- Returns the space of values such that the predicate returns True for element
-- -- at the given index, and, possibly other such elements.
-- index :: (a -> Bool) -> Space a -> Integer -> Integer -> Space a
-- index pred s@(f :$: subspace) size idx =
--   case valid pred' of
--     Just _  -> s
--     Nothing -> f :$: index pred' subspace size idx
--   where
--     pred' = pred . f
-- index pred space size idx = undefined

cross :: ValueSet a -> ValueSet b -> ValueSet (a, b)
cross _ EmptySet        = EmptySet
cross a (Singleton x)   = FMap (\a' -> (a', x)) a
cross a (Union _ b c)   = (a `mkProduct` b) `mkUnion` (a `mkProduct` c) -- distributivity
cross a (Product _ b c) = FMap (\((x, y), z) -> (x, (y, z))) ((a `mkProduct` b) `mkProduct` c) -- associativity
cross a (FMap f set)    = FMap (\(a', x) -> (a', f x)) $ cross a set

indexPred :: (a -> Bool) -> ValueSet a -> Integer -> (Maybe a, ValueSet a)
indexPred _ EmptySet      _ = error "cannot index into empty set"
indexPred p set@(Singleton x) 0
  | p x       = (Just x, set)
  | otherwise = (Nothing, EmptySet)
indexPred _ (Singleton _) _ = error "cannot take nonzero index out of singleton set"
indexPred p (Union _ left right) k
  | k < valueSetSize left =
    let (x, left') = indexPred p left k
    in (x, left' `mkUnion` right)
  | otherwise             =
    let (x, right') = indexPred p right (k - valueSetSize left)
    in (x, left `mkUnion` right')
indexPred p (Product _ v v') k
  | inspectsRight p = indexPred p (swap `FMap` cross v' v) k
  | otherwise       = indexPred p (cross v v') k
indexPred p (FMap f v) k =
  case valid p' of
    Nothing ->
      let (x, v') = indexPred p' v k
      in (f <$> x, FMap f v')
    Just False -> (Nothing, EmptySet)
    Just True  ->
      let (x, v') = indexPred (const True) v k
      in (f <$> x, FMap f v')
  where
    p' = p . f

newtype GenMT g v m a = GenMT (ReaderT (v -> Bool) (StateT (ValueSet v, g) m) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (v -> Bool)
           , MonadState (ValueSet v, g)
           -- , MonadTrans
           , MonadIO
           )

runGenMT :: (RandomGen g, Monad m) => GenMT g v m a -> (v -> Bool) -> ValueSet v -> g -> m a
runGenMT (GenMT action) p set gen = do
  (x, (_set', _gen')) <- runStateT (runReaderT action p) (set, gen)
  return x

randomValue :: (RandomGen g) => GenMT g v IO (Maybe v)
randomValue = do
  (set, gen) <- get
  p          <- ask
  let (n, gen') = randomR (0, valueSetSize set) gen
  liftIO $ putStrLn $ "n = " ++ show n
  liftIO $ putStrLn $ "size: " ++ show (valueSetSize set)
  liftIO $ hFlush stdout
  let (x, set') = indexPred p set n
  liftIO $ putStrLn $ "size: " ++ show (valueSetSize set) ++ " -> " ++ show (valueSetSize set')
  liftIO $ hFlush stdout
  put (set', gen')
  case x of
    Nothing ->
      if valueSetSize set' == 0
      then return Nothing
      else randomValue
    Just x' -> return $ Just x'


main :: IO ()
main = do
  -- putStrLn $ show $ sizedSet 5 natSpace
  -- putStrLn $ show $ reifyValues (sizedSet 10 $ listSpace natSpace)
  gen <- getStdGen
  xs  <- runGenMT (replicateM 1 randomValue) isListSorted (sizedSet 22 $ listSpace (natSpace ())) gen
  putStrLn $ "some sorted lists: " ++ show xs
  return ()
