{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module SortedListGenerator where

import Control.Applicative
import Control.Monad
import Data.Typeable
import System.Environment

import Enumeration

enumerateBool :: Enumeration Bool
enumerateBool = pay $ singleton True `union` singleton False

enumerateList :: Enumeration a -> Enumeration [a]
-- enumerateList x = pay $ singleton [] `union` ((:) <$> x <*> enumerateList x)
enumerateList x = enum
  where
    enum = pay $ singleton [] `union` ((:) <$> x <*> enum)

boolLists :: () -> Enumeration [Bool]
boolLists () = enumerateList enumerateBool

isListSorted :: (Ord a, Show a) => [a] -> Bool
isListSorted []             = True
isListSorted [_]            = True
isListSorted (x1:xs@(x2:_)) = x1 <= x2 && isListSorted xs


main :: IO ()
main = do
  args <- getArgs
  case args of
    -- [n]    -> putStrLn $ show $ indexAbs (read n) boolLists
    -- [p, q] -> putStrLn $ show $ indexAbs (read p ^ read q) boolLists
    [n]    -> putStrLn $ show $ indexPred (read n) isListSorted boolLists
    [p, q] -> putStrLn $ show $ indexPred (read p ^ read q) isListSorted boolLists

