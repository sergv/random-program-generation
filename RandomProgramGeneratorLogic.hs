----------------------------------------------------------------------------
-- |
-- Module      :  RandomProgramGeneratorLogic
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-do-bind  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults   #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing  #-}

module RandomProgramGeneratorLogic where

import Control.Monad (forM_)
import qualified Control.Monad as Monad
import Data.HUtils
import Data.String
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as TIO
import Language.HKanren.Functions.List
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import System.Environment
import Text.PrettyPrint.Leijen.Text (Pretty)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.List (genericLength, zip)
import Prelude (IO, return, fail, ($), fromInteger, read, (.), fromRational, show, (++), putStrLn)

import LogicGeneratorTypes

import Debug.Trace
import Data.List (intercalate)

-- redefine the syntax
(>>) :: Predicate ProgramF -> Predicate ProgramF -> Predicate ProgramF
(>>) = conj

(>>=) :: (TypeI (ProgramF Program) ix)
      => Fresh ix
      -> (Term ProgramF ix -> Predicate ProgramF)
      -> Predicate ProgramF
(>>=) = fresh

validFunction :: Program Function -> Predicate ProgramF
validFunction prog =
  manyFresh $ \name args body retExpr -> do
    args === vars
    prog ==^ Function name args body retExpr
    declaredVars <- Fresh
    let knownFuncs = iCons name iNil
    foldlo (\x -> validStatement x knownFuncs) args body declaredVars
    validExpression declaredVars knownFuncs retExpr
    allUnique args
  where
    vars :: Program (List Name)
    vars = list [iNameF 1, iNameF 2, iNameF 3]

validFunction' :: Program Function -> Predicate ProgramF
validFunction' prog =
  manyFresh $ \name args retExpr -> do
    args === vars
    prog ==^ Function name args iNil retExpr
    let knownFuncs = iCons name iNil
    validExpression args knownFuncs retExpr
    allUnique args
  where
    vars :: Program (List Name)
    vars = list [iNameF 1, iNameF 2, iNameF 3]

validStatement
  :: Program (List Name)
  -> Program (List Name)
  -> Program Statement
  -> Program (List Name)
  -> Predicate ProgramF
validStatement vars knownFuncs stmt outVars =
  conde
    (manyFresh $ \name -> do
       stmt ==^ Declaration name
       isUndeclaredVariable name vars
       outVars ==^ Cons name vars)
    (manyFresh $ \name expr -> do
       stmt ==^ Assignment name expr
       isDeclaredVariable name vars
       validExpression outVars knownFuncs expr
       outVars === outVars)
    (manyFresh $ \cond body -> do
      stmt ==^ While cond body
      validExpression outVars knownFuncs cond
      foldlo (\x -> validStatement x knownFuncs) vars body outVars)

validExpression
  :: Program (List Name)
  -> Program (List Name)
  -> Program Expr
  -> Predicate ProgramF
validExpression vars knownFuncs expr =
  conde
    (manyFresh $ \name -> do
      expr ==^ Var name
      isDeclaredVariable name vars)
    (manyFresh $ \x y -> do
      expr ==^ Add x y
      validExpression vars knownFuncs x
      validExpression vars knownFuncs y)
    (manyFresh $ \x y -> do
      expr ==^ Mul x y
      validExpression vars knownFuncs x
      validExpression vars knownFuncs y)
    (manyFresh $ \x -> do
      expr ==^ IsTrue x
      validExpression vars knownFuncs x)
    (manyFresh $ \c t f -> do
      expr ==^ If c t f
      validExpression vars knownFuncs c
      validExpression vars knownFuncs t
      validExpression vars knownFuncs f)
    -- (manyFresh $ \name args -> do
    --   expr ==^ Funcall name args
    --   member name knownFuncs
    --   allo (validExpression vars knownFuncs) args)

-- validExpression
--   :: Program (List Name)
--   -> Program (List Name)
--   -> Program Expr
--   -> Predicate ProgramF
-- validExpression vars knownFuncs expr = do
--   -- trace (intercalate ", " ["vars = " ++ hshow vars, "knownFuncs = " ++ hshow knownFuncs, "expr = " ++ hshow expr]) $
--   vs <- Fresh
--   isExpr expr
--   exprVars expr iNil vs
--   allo (`isDeclaredVariable` vars) vs
--   where
--     isExpr expr =
--       conde
--         (manyFresh $ \name -> do
--           expr ==^ Var name
--           )
--         (manyFresh $ \x y -> do
--           expr ==^ Add x y
--           isExpr x
--           isExpr y)
--         -- (manyFresh $ \x y -> do
--         --   expr ==^ Mul x y
--         --   validExpression vars knownFuncs x
--         --   validExpression vars knownFuncs y)
--         -- (manyFresh $ \x -> do
--         --   expr ==^ IsTrue x
--         --   validExpression vars knownFuncs x)
--         -- (manyFresh $ \c t f -> do
--         --   expr ==^ If c t f
--         --   validExpression vars knownFuncs c
--         --   validExpression vars knownFuncs t
--         --   validExpression vars knownFuncs f)
--         -- (manyFresh $ \name args -> do
--         --   expr ==^ Funcall name args
--         --   member name knownFuncs
--         --   allo (validExpression vars knownFuncs) args)
--
-- exprVars
--   :: Program Expr
--   -> Program (List Name)
--   -> Program (List Name)
--   -> Predicate ProgramF
-- exprVars expr vs outVs =
--   conde
--     (manyFresh $ \name -> do
--       expr  ==^ Var name
--       outVs ==^ Cons name vs)
--     (manyFresh $ \x y -> do
--       expr ==^ Add x y
--       vs' <- Fresh
--       exprVars x vs vs'
--       exprVars y vs' outVs)
--     -- (manyFresh $ \x y -> do
--     --   expr ==^ Mul x y
--     --   validExpression vars knownFuncs x
--     --   validExpression vars knownFuncs y)
--     -- (manyFresh $ \x -> do
--     --   expr ==^ IsTrue x
--     --   validExpression vars knownFuncs x)
--     -- (manyFresh $ \c t f -> do
--     --   expr ==^ If c t f
--     --   validExpression vars knownFuncs c
--     --   validExpression vars knownFuncs t
--     --   validExpression vars knownFuncs f)
--     -- (manyFresh $ \name args -> do
--     --   expr ==^ Funcall name args
--     --   member name knownFuncs
--     --   allo (validExpression vars knownFuncs) args)


isUndeclaredVariable
  :: Program Name
  -> Program (List Name)
  -> Predicate ProgramF
isUndeclaredVariable = notMember

isDeclaredVariable
  :: Program Name
  -> Program (List Name)
  -> Predicate ProgramF
isDeclaredVariable = member


hdisplay :: (HPretty a) => a ix -> Text
hdisplay = PP.displayT . PP.renderPretty 0.9 100 . hpretty

display :: (Pretty a) => a -> Text
display = PP.displayT . PP.renderPretty 0.9 100 . PP.pretty

main :: IO ()
main = do
  args <- getArgs
  case args of
    [x] -> do
      let funcs = runN (read x) validFunction
      -- let funcs = runN (read x) (validExpression vars funcSet)
      forM_ (zip [0..] funcs) $ \(n, (func, neqs)) -> do
        -- TIO.putStrLn $ T.pack $ hshow func
        putStrLn $ show n
        TIO.putStrLn $ hdisplay func
        putStrLn $ "# of neqs = " ++ show (genericLength neqs)
        TIO.putStrLn $ T.replicate 10 "-"
    _ ->
        TIO.putStrLn $ T.pack $ "invalid arguments: " ++ show args
  return ()
  where
    (>>) = (Monad.>>)
    (>>=) = (Monad.>>=)

    -- vars :: Program (List Name)
    -- vars = list [iNameF 1, iNameF 2, iNameF 3]
    -- funcSet :: Program (List Name)
    -- funcSet = list [iNameF 10]
