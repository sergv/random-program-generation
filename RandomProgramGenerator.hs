{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE DeriveFoldable           #-}
{-# LANGUAGE DeriveTraversable        #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE TypeSynonymInstances     #-}
{-# LANGUAGE UndecidableInstances     #-}

module RandomProgramGenerator where

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Concurrent
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (Foldable)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as TIO
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Data.Set (Set)
import qualified Data.Set as S
import System.Environment
-- import System.Timeout

import Text.PrettyPrint.Leijen.Text hiding ((<>), (<$>))
import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.Random.Source.PureMT (pureMT)

import Enumeration

import Prelude hiding (product)


newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance (Show (f (Fix f))) => Show (Fix f)
deriving instance (Eq (f (Fix f))) => Eq (Fix f)
deriving instance (Ord (f (Fix f))) => Ord (Fix f)

cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . unFix

cataM :: (Traversable f, Monad m) => (f a -> m a) -> Fix f -> m a
cataM alg = alg <=< T.mapM (cataM alg) . unFix

-- All names must be declared before use
newtype Name = Name Int
  deriving (Show, Eq, Ord)

data ExprF e =
    Var Name
  | Add e e
  | Mul e e
  | IsTrue e
  | If e e e
  | Funcall Name [e]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type Expr = Fix ExprF

data Statement =
    Declaration Name
  | Assignment Name Expr
  | While Expr [Statement]
  deriving (Show, Eq, Ord)

data Function = Function Name [Name] [Statement] Expr -- function name, args, body, return expr
  deriving (Show, Eq, Ord)

functionName :: Function -> Name
functionName (Function name _ _ _) = name

functionArity :: Function -> Int
functionArity (Function _ args _ _) = length args

data Program = Program Function [Function] -- main function and other functions
  deriving (Show, Eq, Ord)

instance Pretty Name where
  pretty (Name x) = "@" <> int x

instance Pretty Expr where
  pretty = cata alg
    where
      alg :: ExprF Doc -> Doc
      alg (Var name) = pretty name
      alg (Add x y) = parens $ x <+> "+" <+> y
      alg (Mul x y) = parens $ x <+> "*" <+> y
      alg (IsTrue x) = lbrace <> x <> rbrace
      alg (If c t f) = parens $ group $ align $ "if" <+> c PP.<$> "then" <+> t PP.<$> "else" <+> f
      alg (Funcall name args) = pretty name <> parens (sep $ punctuate PP.comma args)

instance Pretty Statement where
  pretty (Declaration name) = "declare" <+> pretty name
  pretty (Assignment name expr) = pretty name <+> ":=" <+> pretty expr
  pretty (While cond body) =
    "while" <+> parens (pretty cond) <+>
      cbraces (indent 2 (vsep $ map (\stmt -> pretty stmt <> ";") body))

instance Pretty Function where
  pretty (Function name args body retExpr) =
    "function" <+> pretty name <> parens (sep $ punctuate PP.comma $ map pretty args) <+>
    cbraces (indent 2 $ vsep $ map pretty body ++ ["return" <+> pretty retExpr])

instance Pretty Program where
  pretty (Program mainFunc funcs) =
    pretty mainFunc PP.<$> vsep (map pretty funcs)

cbraces :: Doc -> Doc
cbraces x = lbrace PP.<$> indent 2 x PP.<$> rbrace

enumerateList :: Enumeration a -> Enumeration [a]
enumerateList x = enum
  where
    enum = pay $ singleton [] `union` ((:) <$> x <*> enum)

enumerateProgram :: () -> Enumeration Program
enumerateProgram _ = Program <$> enumerateFunction <*> enumerateList enumerateFunction
  where
    enumerateName :: Enumeration Name
    enumerateName = pay $ sum1 $ map (singleton . Name) [0..10]

    enumerateExprF :: Enumeration Expr -> Enumeration (ExprF Expr)
    enumerateExprF e = pay $ sum1 $
      [ Var <$> enumerateName
      , Add <$> e <*> e
      , Mul <$> e <*> e
      , IsTrue <$> e
      , If <$> e <*> e <*> e
      , Funcall <$> enumerateName <*> enumerateList e
      ]

    enumerateExpr :: Enumeration Expr
    enumerateExpr = enm
      where
        enm = Fix <$> enumerateExprF enm

    enumerateStatement :: Enumeration Statement
    enumerateStatement = pay $ sum1 $
      [ Declaration <$> enumerateName
      , Assignment <$> enumerateName <*> enumerateExpr
      , While <$> enumerateExpr <*> stmts
      ]

    stmts :: Enumeration [Statement]
    stmts = enumerateList enumerateStatement

    enumerateFunction :: Enumeration Function
    enumerateFunction =
      (\(a, (b, (c, d))) -> Function a d b c) <$>
        (enumerateName `product`
         (stmts `product`
          (enumerateExpr `product`
           enumerateList enumerateName)))
      -- natural enumeration
      -- Function
      --   <$> enumerateName
      --   <*> enumerateList enumerateName
      --   <*> stmts
      --   <*> enumerateExpr
      -- efficient enumeration
      -- (\name body ret args -> Function name args body ret)
      --   <$> enumerateName
      --   <*> stmts
      --   <*> enumerateExpr
      --   <*> enumerateList enumerateName

validProgram :: Program -> Bool
validProgram (Program f fs) =
  allUnique funcNames &&
  validFunction funcArities f &&
  all (validFunction funcArities) fs
  where
    funcNames = functionName f : map functionName fs
    funcArities :: Map Name Int
    funcArities = M.fromList $ map (functionName &&& functionArity) $ f : fs

allUnique :: (Ord a) => [a] -> Bool
allUnique xs = S.size (S.fromList xs) == length xs


type CheckM = ErrorT String (ReaderT (Map Name Int) (State (Set Name)))

isDefinedFunction :: (MonadReader (Map Name Int) m) => Name -> m (Maybe Int)
isDefinedFunction name = asks (M.lookup name)

addDeclaredVariable :: (MonadState (Set Name) m) => Name -> m ()
addDeclaredVariable name = modify (S.insert name)

isDeclaredVariable :: (MonadState (Set Name) m) => Name -> m Bool
isDeclaredVariable name = gets (S.member name)

validFunction :: Map Name Int -> Function -> Bool
validFunction arities (Function _ args body ret) =
  allUnique args &&
  either (const False) (const True) res
  where
    res :: Either String ()
    res = evalState
            (runReaderT
               (runErrorT go)
               arities)
            (S.fromList args)
    go = mapM_ checkStatement body >> checkExpr ret

checkStatement :: Statement -> CheckM ()
checkStatement (Declaration name) = do
  declared <- isDeclaredVariable name
  if declared
  then throwError $ "variable " ++ show name ++ " redeclared"
  else addDeclaredVariable name
checkStatement (Assignment name expr) = do
  declared <- isDeclaredVariable name
  unless declared $
    throwError $ "undeclared variable " ++ show name ++ " in assignment"
  checkExpr expr
checkStatement (While cond body) = do
  checkExpr cond
  mapM_ checkStatement body

checkExpr :: Expr -> CheckM ()
checkExpr = cataM alg
  where
    alg :: ExprF () -> CheckM ()
    alg (Var name)       = do
      declared <- isDeclaredVariable name
      unless declared $
        throwError $ "reading of undeclared variable " ++ show name
    alg (Add _ _)        = return ()
    alg (Mul _ _)        = return ()
    alg (IsTrue _)       = return ()
    alg (If _c _t _f)    = return ()
    alg (Funcall name args) = do
      arity <- isDefinedFunction name
      case arity of
        Nothing -> throwError $ "call to unknown function " ++ show name
        Just n
          | n == length args -> return ()
          | otherwise        -> throwError $ "function " ++ show name ++ " called with wrong number of arguments"


display :: (Pretty a) => a -> Text
display = PP.displayT . renderPretty 0.9 100 . pretty

printChan :: (Pretty a) => Chan a -> IO ()
printChan chan = do
  x <- readChan chan
  TIO.putStrLn $ display x
  printChan chan

main :: IO ()
main = do
  args <- getArgs
  putStrLn "Functions:"
  -- res <- timeout (10 * 10000) $
  case args of
    -- [n]    -> putStrLn $ show $ indexAbs (read n) boolLists
    -- [p, q] -> putStrLn $ show $ indexAbs (read p ^ read q) boolLists
    [n]    -> do
      let mt =  pureMT 1
      mapM_ (TIO.putStrLn . display) $
        generateRandomValues (parts (enumerateProgram ()) !! read n) validProgram mt 1000000
    [p, q] -> do
      caps <- getNumCapabilities
      let mts = map (pureMT . fromIntegral) [1..caps]
      putStrLn $ "starting " ++ show caps ++ " threads"
      chan <- newChan
      let enums = parts (enumerateProgram ()) !! read p
        in forM_ mts $ \mt ->
             forkIO $
               forM_ (generateRandomValues enums validProgram mt (read q)) $ \x ->
                 writeChan chan x

      printChan chan

    [p, q, seed] -> do
      let mt = pureMT $ read seed
      mapM_ (TIO.putStrLn . display) $
        generateRandomValues (parts (enumerateProgram ()) !! read p) validProgram mt (read q)

    _      -> error $ "invalid arguments: " ++ unwords args
  -- case res of
  --   Nothing -> putStrLn "timed out"
  --   _       -> return ()

-- main :: IO ()
-- main = do
--   args <- getArgs
--   putStrLn "Function:"
--   PP.displayIO stdout $ renderPretty 0.9 100 $ either (PP.text . T.pack) pretty $
--     case args of
--       -- [n]    -> putStrLn $ show $ indexAbs (read n) boolLists
--       -- [p, q] -> putStrLn $ show $ indexAbs (read p ^ read q) boolLists
--       [n]    -> indexPred (read n) validProgram enumerateProgram
--       [p, q] -> indexPred (read p ^ read q) validProgram enumerateProgram
--   putStrLn ""
--   putStrLn $ replicate 20 '-'
