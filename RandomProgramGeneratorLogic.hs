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

{-# LANGUAGE DoAndIfThenElse     #-}
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
import Control.Monad.Reader (Reader, runReader)
import Control.Monad.State (State, evalState)
import Data.Functor.Identity
import Data.HUtils
import Data.Proxy
import Data.Random.Source.PureMT (PureMT, pureMT)
import Data.String
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as TIO
import Language.HKanren.Functions.List
import Language.HKanren.Functions.Nat
import Language.HKanren.Nondeterminism
import Language.HKanren.Syntax
import Language.HKanren.Types.List
import Language.HKanren.Types.Nat
import System.Environment
import Text.PrettyPrint.Leijen.Text (Pretty)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.List (genericLength, zip, null)
import Prelude (Int, Bool(..), IO, return, fail, ($), fromInteger, read, (.), fromRational, show, (++), putStrLn)

import LogicGeneratorTypes

import Debug.Trace

default (Int)

argVars :: Program (List Name)
argVars = list [iNameF 1, iNameF 2, iNameF 3]

validFunction :: Program Function -> Predicate ProgramVar
validFunction prog =
  fresh $ \name args body retExpr declaredVars -> do
    args === argVars
    prog ==^ Function name args body retExpr
    let knownFuncs = iCons name iNil
    validStatement args knownFuncs body declaredVars
    validExpression declaredVars knownFuncs retExpr
    allUnique args

validFunction' :: Program Function -> Predicate ProgramVar
validFunction' prog =
  fresh $ \name args body retExpr -> do
    args === argVars
    prog ==^ Function name args body retExpr
    let knownFuncs = iCons name iNil
    validExpression args knownFuncs retExpr
    allUnique args
  where
    argVars :: Program (List Name)
    argVars = list [iNameF 1, iNameF 2]

validStatement
  :: Program (List Name)
  -> Program (List Name)
  -> Program Statement
  -> Program (List Name)
  -> Predicate ProgramVar
validStatement argVars knownFuncs stmt outVars =
  conde
    -- (fresh $ \name -> do
    --   stmt ==^ Declaration name
    --   isUndeclaredVariable name argVars
    --   outVars ==^ Cons name argVars)
    (fresh $ \stmts -> do
      stmt ==^ Block stmts
      foldlo' argVars stmts outVars $ \acc x out ->
        validStatement acc knownFuncs x out)
    (fresh $ \name expr -> do
      stmt ==^ Assignment name expr
      isDeclaredVariable name argVars
      validExpression argVars knownFuncs expr
      outVars ==^ Cons name argVars)
    (fresh $ \cond body -> do
      stmt ==^ While cond body
      validExpression argVars knownFuncs cond
      validStatement argVars knownFuncs body outVars)

validExpression
  :: Program (List Name)
  -> Program (List Name)
  -> Program Expr
  -> Predicate ProgramVar
validExpression argVars knownFuncs expr =
  conde
    (fresh $ \name -> do
      expr ==^ Var name
      isDeclaredVariable name argVars)
    (fresh $ \x y -> do
      expr ==^ Add x y
      validExpression argVars knownFuncs x
      validExpression argVars knownFuncs y)
    (fresh $ \x y -> do
      expr ==^ Mul x y
      validExpression argVars knownFuncs x
      validExpression argVars knownFuncs y)
    (fresh $ \x -> do
      expr ==^ IsTrue x
      validExpression argVars knownFuncs x)
    (fresh $ \c t f -> do
      expr ==^ If c t f
      validExpression argVars knownFuncs c
      validExpression argVars knownFuncs t
      validExpression argVars knownFuncs f)
    -- (fresh $ \name args -> do
    --   expr ==^ Funcall name args
    --   member name knownFuncs
    --   allo (validExpression argVars knownFuncs) args)

statementSize
  :: Program Statement
  -> Program Nat
  -> Predicate ProgramVar
statementSize stmt n =
  conde
    (fresh $ \name expr m -> do
      stmt ==^ Assignment name expr
      n ==^ S m
      exprSize expr m)
    (fresh $ \stmts k -> do
      stmt ==^ Block stmts
      plus1 k n
      foldlo' iZ stmts k $ \acc x out -> do
        xSize <- statementSize x
        pluso acc xSize out)
    (fresh $ \cond body m k mk -> do
      stmt ==^ While cond body
      n ==^ S (iS mk)
      exprSize cond m
      statementSize body k
      pluso m k mk)

exprSize
  :: Program Expr
  -> Program Nat
  -> Predicate ProgramVar
exprSize expr n = do
  n =/^ Z
  conde
    (fresh $ \name -> do
      expr ==^ Var name
      n    ==^ S iZ)
    (fresh $ \x y -> do
      expr ==^ Add x y
      m <- exprSize x
      k <- exprSize y
      pluso m k n)
    (fresh $ \x y -> do
      expr ==^ Mul x y
      m <- exprSize x
      k <- exprSize y
      pluso m k n)
    (fresh $ \x -> do
      expr ==^ IsTrue x
      m <- exprSize x
      plus1 m n)
    (fresh $ \c t f -> do
      expr ==^ If c t f
      m <- exprSize c
      k <- exprSize t
      q <- exprSize f
      plus3o m k q n)
    -- (fresh $ \name args -> do
    --   expr ==^ Funcall name args
    --   member name knownFuncs
    --   allo (validExpression argVars knownFuncs) args)

validSizedFunctionNaive :: Program Nat -> Program Function -> Predicate ProgramVar
validSizedFunctionNaive n prog =
  fresh $ \name args body retExpr bodySize retSize declaredVars -> do
    args === argVars
    prog ==^ Function name args body retExpr
    bodyPlusRetSize <- pluso bodySize retSize
    plus1 bodyPlusRetSize n
    statementSize body bodySize
    exprSize retExpr retSize
    let knownFuncs = iCons name iNil
    validStatement args knownFuncs body declaredVars
    validExpression declaredVars knownFuncs retExpr
    allUnique args


validSizedFunction :: Program Nat -> Program Function -> Predicate ProgramVar
validSizedFunction n prog =
  fresh $ \name args body retExpr bodySize retSize declaredVars m -> do
    args === argVars
    prog ==^ Function name args body retExpr

    let knownFuncs = iCons name iNil
    plus1 m n
    m =/^ Z
    pluso bodySize retSize m
    bodySize =/^ Z
    retSize  =/^ Z
    validSizedBlock args knownFuncs body declaredVars bodySize
    validSizedExpression declaredVars knownFuncs retExpr retSize
    allUnique args

validSizedBlock
  :: Program (List Name)
  -> Program (List Name)
  -> Program Statement
  -> Program (List Name)
  -> Program Nat
  -> Predicate ProgramVar
validSizedBlock argVars knownFuncs stmt outVars outSize = do
  (fresh $ \stmts k -> do
    stmt ==^ Block stmts
    k =/^ Z
    plus1 k outSize
    foldl2o' argVars iZ stmts outVars k $ \vars size x vars' size' -> do
      fresh $ \m -> do
        m =/^ Z
          trace ("validSizedBlock: Block 5, size = " ++ display size') success
        pluso m size size'
          trace ("validSizedBlock: Block 6, m = " ++ display m') success
        validSizedStatement vars knownFuncs x vars' m)

validSizedStatement
  :: Program (List Name)
  -> Program (List Name)
  -> Program Statement
  -> Program (List Name)
  -> Program Nat
  -> Predicate ProgramVar
validSizedStatement argVars knownFuncs stmt outVars outSize = do
  outSize =/^ Z
  conde
    -- (fresh $ \name -> do
    --   stmt ==^ Declaration name
    --   isUndeclaredVariable name argVars
    --   outVars ==^ Cons name argVars)
    (fresh $ \name expr m -> do
      stmt    ==^ Assignment name expr
      m       =/^ Z
      plus1 m outSize
      isDeclaredVariable name argVars
      validSizedExpression argVars knownFuncs expr m
      outVars ==^ Cons name argVars)
    -- (fresh $ \cond body bodySize -> do
    --   stmt ==^ While cond body
    --   condSize <- validSizedExpression argVars knownFuncs cond
    --   foldl2o' argVars iZ body outVars bodySize $ \vars size x outVars outSize -> do
    --     stmtSize <- validSizedBlock vars knownFuncs x outVars
    --     pluso size stmtSize outSize
    --   m <- pluso condSize bodySize
    --   outSize ==^ S (iS m))


validSizedExpression
  :: Program (List Name)
  -> Program (List Name)
  -> Program Expr
  -> Program Nat
  -> Predicate ProgramVar
validSizedExpression argVars knownFuncs expr outSize = do
  conde
    (fresh $ \name -> do
      expr    ==^ Var name
      isDeclaredVariable name argVars
      outSize ==^ S iZ)
    (fresh $ \x y xSize ySize -> do
      expr  ==^ Add x y
      pluso xSize ySize outSize
      xSize =/^ Z
      ySize =/^ Z
      validSizedExpression argVars knownFuncs x xSize
      validSizedExpression argVars knownFuncs y ySize)
    (fresh $ \x y xSize ySize -> do
      expr ==^ Mul x y
      pluso xSize ySize outSize
      xSize =/^ Z
      ySize =/^ Z
      validSizedExpression argVars knownFuncs x xSize
      validSizedExpression argVars knownFuncs y ySize)
    (fresh $ \x xSize -> do
      expr ==^ IsTrue x
      plus1 xSize outSize
      xSize =/^ Z
      validSizedExpression argVars knownFuncs x xSize)
    (fresh $ \c t f cSize tSize tmp fSize -> do
      expr ==^ If c t f
      cSize =/^ Z
      tSize =/^ Z
      fSize =/^ Z
      tmp =/^ Z
      pluso fSize tmp outSize
      pluso cSize tSize tmp
      validSizedExpression argVars knownFuncs c cSize
      validSizedExpression argVars knownFuncs t tSize
      validSizedExpression argVars knownFuncs f fSize)

    -- (fresh $ \name args -> do
    --   expr ==^ Funcall name args
    --   member name knownFuncs
    --   allo (validExpression argVars knownFuncs) args)


-- validExpression
--   :: Program (List Name)
--   -> Program (List Name)
--   -> Program Expr
--   -> Predicate ProgramVar
-- validExpression argVars knownFuncs expr = do
--   -- trace (intercalate ", " ["argVars = " ++ hshow argVars, "knownFuncs = " ++ hshow knownFuncs, "expr = " ++ hshow expr]) $
--   vs <- Fresh
--   isExpr expr
--   exprVars expr iNil vs
--   allo (`isDeclaredVariable` argVars) vs
--   where
--     isExpr expr =
--       conde
--         (fresh $ \name -> do
--           expr ==^ Var name
--           )
--         (fresh $ \x y -> do
--           expr ==^ Add x y
--           isExpr x
--           isExpr y)
--         -- (fresh $ \x y -> do
--         --   expr ==^ Mul x y
--         --   validExpression argVars knownFuncs x
--         --   validExpression argVars knownFuncs y)
--         -- (fresh $ \x -> do
--         --   expr ==^ IsTrue x
--         --   validExpression argVars knownFuncs x)
--         -- (fresh $ \c t f -> do
--         --   expr ==^ If c t f
--         --   validExpression argVars knownFuncs c
--         --   validExpression argVars knownFuncs t
--         --   validExpression argVars knownFuncs f)
--         -- (fresh $ \name args -> do
--         --   expr ==^ Funcall name args
--         --   member name knownFuncs
--         --   allo (validExpression argVars knownFuncs) args)
--
-- exprVars
--   :: Program Expr
--   -> Program (List Name)
--   -> Program (List Name)
--   -> Predicate ProgramVar
-- exprVars expr vs outVs =
--   conde
--     (fresh $ \name -> do
--       expr  ==^ Var name
--       outVs ==^ Cons name vs)
--     (fresh $ \x y -> do
--       expr ==^ Add x y
--       vs' <- Fresh
--       exprVars x vs vs'
--       exprVars y vs' outVs)
--     -- (fresh $ \x y -> do
--     --   expr ==^ Mul x y
--     --   validExpression argVars knownFuncs x
--     --   validExpression argVars knownFuncs y)
--     -- (fresh $ \x -> do
--     --   expr ==^ IsTrue x
--     --   validExpression argVars knownFuncs x)
--     -- (fresh $ \c t f -> do
--     --   expr ==^ If c t f
--     --   validExpression argVars knownFuncs c
--     --   validExpression argVars knownFuncs t
--     --   validExpression argVars knownFuncs f)
--     -- (fresh $ \name args -> do
--     --   expr ==^ Funcall name args
--     --   member name knownFuncs
--     --   allo (validExpression argVars knownFuncs) args)


isUndeclaredVariable
  :: Program Name
  -> Program (List Name)
  -> Predicate ProgramVar
isUndeclaredVariable = notMember

isDeclaredVariable
  :: Program Name
  -> Program (List Name)
  -> Predicate ProgramVar
isDeclaredVariable = member


hdisplay :: (HPretty a) => a ix -> Text
hdisplay = PP.displayT . PP.renderPretty 0.9 100 . hpretty

display :: (Pretty a) => a -> String
display = T.unpack . PP.displayT . PP.renderPretty 0.9 100 . PP.pretty


-- nondet :: Proxy NondetLogicT
-- nondet = nondetLogicT
--
-- runNondet :: Identity a -> a
-- runNondet = runIdentity

-- nondet :: Proxy NondetDepthFirst
-- nondet = nondetDepthFirst
--
-- runNondet :: Identity a -> a
-- runNondet = runIdentity

-- nondet :: Proxy NondetBreadthFirst -- Randomized
-- nondet = nondetBreadthFirst -- Randomized
--
-- runNondet :: Identity a -> a
-- runNondet = runIdentity

nondet :: Proxy NondetIterativeDeepeningBreadthFirst
nondet = nondetIterativeDeepeningBreadthFirst

runNondet :: Reader Int a -> a
runNondet x = runReader x 10


-- runNondet :: State PureMT a -> a
-- runNondet x = evalState x mt
--   where
--     mt :: PureMT
--     mt = pureMT 0


main :: IO ()
main = do
  args <- getArgs
  case args of
    [x] -> do
      let funcs  = runN nondet (read x) validFunction
          funcs' = runNondet funcs
      -- let funcs = runN nondet (read x) (validExpression argVars funcSet)
      -- let funcs = runN nondet (read x) (validExpression argVars funcSet)
      forM_ (zip [0..] funcs') $ \(n, (func, neqs)) -> do
        -- TIO.putStrLn $ T.pack $ hshow func
        putStrLn $ "#" ++ show n
        TIO.putStrLn $ hdisplay func
        putStrLn $ "# of neqs = " ++ show (genericLength neqs)
        TIO.putStrLn $ T.replicate 10 "-"
    [x, y] -> do
      -- let funcs = runN nondet (read x) $ \q -> validSizedFunction (int2nat (read y)) q
      let funcs  = runN nondet (read x) $ \q -> validSizedFunctionNaive (int2nat (read y)) q
          funcs' = runNondet funcs
      -- let funcs = runN nondet (read x) $ \q -> statementSize q $ int2nat (read y)
      if null funcs'
      then
        putStrLn "No results"
      else
        forM_ (zip [0..] funcs') $ \(n, (func, neqs)) -> do
          -- TIO.putStrLn $ T.pack $ hshow func
          putStrLn $ "#" ++ show n
          TIO.putStrLn $ hdisplay func
          putStrLn $ "# of neqs = " ++ show (genericLength neqs)
          TIO.putStrLn $ T.replicate 10 "-"
    _ ->
        TIO.putStrLn $ T.pack $ "invalid arguments: " ++ show args
  return ()
  where
    (>>) = (Monad.>>)
    (>>=) = (Monad.>>=)
    ifThenElse True t _ = t
    ifThenElse _    _ f = f
