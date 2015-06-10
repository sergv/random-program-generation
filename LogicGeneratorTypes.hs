----------------------------------------------------------------------------
-- |
-- Module      :  LogicGeneratorTypes
-- Copyright   :  (c) Sergey Vinokurov 2015
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

-- needed for standalone instances
{-# LANGUAGE UndecidableInstances #-}

module LogicGeneratorTypes where

import Control.Monad
import Data.HOrdering
import Data.HUtils
import Data.Monoid
import Data.Type.Equality
import Language.HKanren
import Language.HKanren.Types.Nat
import Language.HKanren.Types.List
-- import qualified Language.HKanren.SafeLVar as Safe
import qualified Language.HKanren.IntegerLVar as Integer
-- import qualified Language.HKanren.IntLVar as Int

import Text.PrettyPrint.Leijen.Text (Doc, (<+>), parens, group, align, lbrace, rbrace, punctuate, sep, vsep)
import qualified Text.PrettyPrint.Leijen.Text as PP

-- newtype Name = Name Int
--   deriving (Show, Eq, Ord)
--
-- instance Pretty Name where
--   pretty (Name x) = PP.int x

-- Names

data Name

-- newtype Name = Name Int
--   deriving (Show, Eq, Ord)
--
-- instance Pretty Name where
--   pretty (Name x) = PP.int x


data NameF :: (* -> *) -> (* -> *) where
  NameF :: Int -> NameF h Name

iNameF :: (NameF :<: LFunctor k) => Int -> Term k Name
iNameF = inject . NameF

instance HEq (NameF h) where
  {-# INLINABLE heq #-}
  heq (NameF x) (NameF y) = x == y

instance HEqHet (NameF h) where
  {-# INLINABLE heqIx #-}
  heqIx (NameF _) (NameF _) = Just Refl

instance HOrd (NameF h) where
  {-# INLINABLE hcompare #-}
  hcompare (NameF x) (NameF y) = compare x y

instance HOrdHet (NameF h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx (NameF _) (NameF _) = {-# SCC hcompareIx_type_NameF #-} HEQ


instance HFunctorId NameF where
  hfmapId _ (NameF x) = NameF x

instance HFoldable NameF where
  hfoldMap _ _ = mempty

instance HShow (NameF h) where
  hshowsPrec n (NameF x) =
    showParen (n == 11) (showString "NameF " . showsPrec 11 x)

instance HPretty (NameF h) where
  hpretty (NameF x) = "@" <> PP.int x


instance Unifiable NameF h where
  unify (NameF x) (NameF y) s
    | x == y    = Just s
    | otherwise = Nothing


instance (ix ~ Name) => TypeI (NameF h) ix where
  type SupportsIx (NameF h) ix = Equal ix Name
  data Type (NameF h) idx where
    TName :: Type (NameF h) Name
  singType = TName

instance HEq (Type (NameF h)) where
  {-# INLINABLE heq #-}
  heq TName TName = True

instance HEqHet (Type (NameF h)) where
  {-# INLINABLE heqIx #-}
  heqIx TName TName = Just Refl

instance HOrd (Type (NameF h)) where
  {-# INLINABLE hcompare #-}
  hcompare TName TName = EQ

instance HOrdHet (Type (NameF h)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx TName TName = {-# SCC hcompareIx_type_TName #-} HEQ

-- Expressions

data Expr

data ExprF h ix where
  Var     :: h Name -> ExprF h Expr
  Add     :: h Expr -> h Expr -> ExprF h Expr
  Mul     :: h Expr -> h Expr -> ExprF h Expr
  IsTrue  :: h Expr -> ExprF h Expr
  If      :: h Expr -> h Expr -> h Expr -> ExprF h Expr
  Funcall :: h Name -> h (List Expr) -> ExprF h Expr

iVar :: (ExprF :<: LFunctor k) => Term k Name -> Term k Expr
iVar = inject . Var

iAdd :: (ExprF :<: LFunctor k) => Term k Expr -> Term k Expr -> Term k Expr
iAdd x y = inject $ Add x y

iMul :: (ExprF :<: LFunctor k) => Term k Expr -> Term k Expr -> Term k Expr
iMul x y = inject $ Mul x y

iIsTrue :: (ExprF :<: LFunctor k) => Term k Expr -> Term k Expr
iIsTrue = inject . IsTrue

iIf :: (ExprF :<: LFunctor k) => Term k Expr -> Term k Expr -> Term k Expr -> Term k Expr
iIf c t f = inject $ If c t f

iFuncall :: (ExprF :<: LFunctor k) => Term k Name -> Term k (List Expr) -> Term k Expr
iFuncall f xs = inject $ Funcall f xs

instance (HEq h) => HEq (ExprF h) where
  {-# INLINABLE heq #-}
  heq (Var x)        (Var x')         = heq x x'
  heq (Add x y)      (Add x' y')      = heq x x' && heq y y'
  heq (Mul x y)      (Mul x' y')      = heq x x' && heq y y'
  heq (IsTrue x)     (IsTrue x')      = heq x x'
  heq (If c t f)     (If c' t' f')    = heq c c' && heq t t' && heq f f'
  heq (Funcall f xs) (Funcall f' xs') = heq f f' && heq xs xs'
  heq _              _                = False

instance (HEq h) => HEqHet (ExprF h) where
  {-# INLINABLE heqIx #-}
  heqIx (Var _) (Var _)       = Just Refl
  heqIx (Var _) (Add _ _)     = Just Refl
  heqIx (Var _) (Mul _ _)     = Just Refl
  heqIx (Var _) (IsTrue _)    = Just Refl
  heqIx (Var _) (If _ _ _)    = Just Refl
  heqIx (Var _) (Funcall _ _) = Just Refl

  heqIx (Add _ _) (Var _)       = Just Refl
  heqIx (Add _ _) (Add _ _)     = Just Refl
  heqIx (Add _ _) (Mul _ _)     = Just Refl
  heqIx (Add _ _) (IsTrue _)    = Just Refl
  heqIx (Add _ _) (If _ _ _)    = Just Refl
  heqIx (Add _ _) (Funcall _ _) = Just Refl

  heqIx (Mul _ _) (Var _)       = Just Refl
  heqIx (Mul _ _) (Add _ _)     = Just Refl
  heqIx (Mul _ _) (Mul _ _)     = Just Refl
  heqIx (Mul _ _) (IsTrue _)    = Just Refl
  heqIx (Mul _ _) (If _ _ _)    = Just Refl
  heqIx (Mul _ _) (Funcall _ _) = Just Refl

  heqIx (IsTrue _) (Var _)       = Just Refl
  heqIx (IsTrue _) (Add _ _)     = Just Refl
  heqIx (IsTrue _) (Mul _ _)     = Just Refl
  heqIx (IsTrue _) (IsTrue _)    = Just Refl
  heqIx (IsTrue _) (If _ _ _)    = Just Refl
  heqIx (IsTrue _) (Funcall _ _) = Just Refl

  heqIx (If _ _ _) (Var _)       = Just Refl
  heqIx (If _ _ _) (Add _ _)     = Just Refl
  heqIx (If _ _ _) (Mul _ _)     = Just Refl
  heqIx (If _ _ _) (IsTrue _)    = Just Refl
  heqIx (If _ _ _) (If _ _ _)    = Just Refl
  heqIx (If _ _ _) (Funcall _ _) = Just Refl

  heqIx (Funcall _ _) (Var _)       = Just Refl
  heqIx (Funcall _ _) (Add _ _)     = Just Refl
  heqIx (Funcall _ _) (Mul _ _)     = Just Refl
  heqIx (Funcall _ _) (IsTrue _)    = Just Refl
  heqIx (Funcall _ _) (If _ _ _)    = Just Refl
  heqIx (Funcall _ _) (Funcall _ _) = Just Refl

instance (HOrd h) => HOrd (ExprF h) where
  {-# INLINABLE hcompare #-}
  hcompare (Var x)        (Var x')         = hcompare x x'
  hcompare (Var _)        _                = LT
  hcompare (Add _ _)      (Var _)          = GT
  hcompare (Add x y)      (Add x' y')      = hcompare x x' <> hcompare y y'
  hcompare (Add _ _)      _                = LT
  hcompare (Mul _ _)      (Var _)          = GT
  hcompare (Mul _ _)      (Add _ _)        = GT
  hcompare (Mul x y)      (Mul x' y')      = hcompare x x' <> hcompare y y'
  hcompare (Mul _ _)      _                = GT
  hcompare (IsTrue _)     (Var _)          = GT
  hcompare (IsTrue _)     (Add _ _)        = GT
  hcompare (IsTrue _)     (Mul _ _)        = GT
  hcompare (IsTrue x)     (IsTrue x')      = hcompare x x'
  hcompare (IsTrue _)     _                = LT
  hcompare (If _ _ _)     (Var _)          = GT
  hcompare (If _ _ _)     (Add _ _)        = GT
  hcompare (If _ _ _)     (Mul _ _)        = GT
  hcompare (If _ _ _)     (IsTrue _)       = GT
  hcompare (If c t f)     (If c' t' f')    = hcompare c c' <> hcompare t t' <> hcompare f f'
  hcompare (If _ _ _)     (Funcall _ _)    = GT
  hcompare (Funcall f xs) (Funcall f' xs') = hcompare f f' <> hcompare xs xs'
  hcompare (Funcall _ _)  _                = GT


instance (HOrd h) => HOrdHet (ExprF h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx x y = {-# SCC hcompareIx_type_ExprF #-} go x y
    where
      go :: ExprF h ix -> ExprF h ix' -> HOrdering ix ix'
      go (Var _) (Var _)       = HEQ
      go (Var _) (Add _ _)     = HEQ
      go (Var _) (Mul _ _)     = HEQ
      go (Var _) (IsTrue _)    = HEQ
      go (Var _) (If _ _ _)    = HEQ
      go (Var _) (Funcall _ _) = HEQ

      go (Add _ _) (Var _)       = HEQ
      go (Add _ _) (Add _ _)     = HEQ
      go (Add _ _) (Mul _ _)     = HEQ
      go (Add _ _) (IsTrue _)    = HEQ
      go (Add _ _) (If _ _ _)    = HEQ
      go (Add _ _) (Funcall _ _) = HEQ

      go (Mul _ _) (Var _)       = HEQ
      go (Mul _ _) (Add _ _)     = HEQ
      go (Mul _ _) (Mul _ _)     = HEQ
      go (Mul _ _) (IsTrue _)    = HEQ
      go (Mul _ _) (If _ _ _)    = HEQ
      go (Mul _ _) (Funcall _ _) = HEQ

      go (IsTrue _) (Var _)       = HEQ
      go (IsTrue _) (Add _ _)     = HEQ
      go (IsTrue _) (Mul _ _)     = HEQ
      go (IsTrue _) (IsTrue _)    = HEQ
      go (IsTrue _) (If _ _ _)    = HEQ
      go (IsTrue _) (Funcall _ _) = HEQ

      go (If _ _ _) (Var _)       = HEQ
      go (If _ _ _) (Add _ _)     = HEQ
      go (If _ _ _) (Mul _ _)     = HEQ
      go (If _ _ _) (IsTrue _)    = HEQ
      go (If _ _ _) (If _ _ _)    = HEQ
      go (If _ _ _) (Funcall _ _) = HEQ

      go (Funcall _ _) (Var _)       = HEQ
      go (Funcall _ _) (Add _ _)     = HEQ
      go (Funcall _ _) (Mul _ _)     = HEQ
      go (Funcall _ _) (IsTrue _)    = HEQ
      go (Funcall _ _) (If _ _ _)    = HEQ
      go (Funcall _ _) (Funcall _ _) = HEQ


instance HFunctorId ExprF where
  hfmapId g (Var x)        = Var (g x)
  hfmapId g (Add x y)      = Add (g x) (g y)
  hfmapId g (Mul x y)      = Mul (g x) (g y)
  hfmapId g (IsTrue x)     = IsTrue (g x)
  hfmapId g (If c t f)     = If (g c) (g t) (g f)
  hfmapId g (Funcall f xs) = Funcall (g f) (g xs)

instance HFoldable ExprF where
  hfoldMap g (Var x)        = g x
  hfoldMap g (Add x y)      = g x <> g y
  hfoldMap g (Mul x y)      = g x <> g y
  hfoldMap g (IsTrue x)     = g x
  hfoldMap g (If c t f)     = g c <> g t <> g f
  hfoldMap g (Funcall f xs) = g f <> g xs

instance (HShow h) => HShow (ExprF h) where
  hshowsPrec n (Var name)  =
    showParen (n == 11) (showString "Var " . hshowsPrec 11 name)
  hshowsPrec n (Add x y) =
    showParen
      (n == 11)
      (showString "Add " . hshowsPrec 11 x . showString " " . hshowsPrec 11 y)
  hshowsPrec n (Mul x y) =
    showParen
      (n == 11)
      (showString "Mul " . hshowsPrec 11 x . showString " " . hshowsPrec 11 y)
  hshowsPrec n (IsTrue x) =
    showParen
      (n == 11)
      (showString "IsTrue " . hshowsPrec 11 x)
  hshowsPrec n (If c t f) =
    showParen
      (n == 11)
      (showString "If " . hshowsPrec 11 c . showString " " . hshowsPrec 11 t . showString " " . hshowsPrec 11 f)
  hshowsPrec n (Funcall f xs) =
    showParen
      (n == 11)
      (showString "Funcall " . hshowsPrec 11 f . showString " " . hshowsPrec 11 xs)

instance (HPretty h, ReifyList h h) => HPretty (ExprF h) where
  hpretty (Var name)     = hpretty name
  hpretty (Add x y)      = parens $ hpretty x <+> "+" <+> hpretty y
  hpretty (Mul x y)      = parens $ hpretty x <+> "*" <+> hpretty y
  hpretty (IsTrue x)     = PP.brackets $ hpretty x
  hpretty (If c t f)     =
    parens $
    group $
    align $
    "if" <+> hpretty c PP.<$>
    "then" <+> hpretty t
    PP.<$> "else" <+> hpretty f
  hpretty (Funcall f xs) =
    hpretty f <>
    parens (sep $ punctuate PP.comma $ map hpretty $ reifyList xs)


instance (Unifiable (LFunctor k) k, HFoldable (LFunctor k), HOrdHet (Term1 k), HOrdHet (Type (Term1 k)), LVar k) => Unifiable ExprF k where
  unify (Var x)        (Var y)        = unifyTerms x y
  unify (Add x y)      (Add x' y')    = unifyTerms x x' >=> unifyTerms y y'
  unify (Mul x y)      (Mul x' y')    = unifyTerms x x' >=> unifyTerms y y'
  unify (IsTrue x)     (IsTrue y)     = unifyTerms x y
  unify (If c t f)     (If c' t' f')  = unifyTerms c c' >=> unifyTerms t t' >=> unifyTerms f f'
  unify (Funcall f xs) (Funcall g ys) = unifyTerms f g >=> unifyTerms xs ys
  unify _              _              = const Nothing



instance (ix ~ Expr) => TypeI (ExprF h) ix where
  type SupportsIx (ExprF h) ix = Equal ix Expr
  data Type (ExprF h) idx where
    TExpr :: Type (ExprF h) Expr
  singType = TExpr

instance HEq (Type (ExprF h)) where
  {-# INLINABLE heq #-}
  heq TExpr TExpr = True

instance HEqHet (Type (ExprF h)) where
  {-# INLINABLE heqIx #-}
  heqIx TExpr TExpr = Just Refl

instance HOrd (Type (ExprF h)) where
  {-# INLINABLE hcompare #-}
  hcompare TExpr TExpr = EQ

instance HOrdHet (Type (ExprF h)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx TExpr TExpr = {-# SCC hcompareIx_type_TExpr #-} HEQ

-- Statements

data Statement

data StatementF h ix where
  Declaration :: h Name -> StatementF h Statement
  Block       :: h (List Statement) -> StatementF h Statement
  Assignment  :: h Name -> h Expr -> StatementF h Statement
  While       :: h Expr -> h Statement -> StatementF h Statement

iDeclaration :: (StatementF :<: LFunctor k) => Term k Name -> Term k Statement
iDeclaration = inject . Declaration

iBlock :: (StatementF :<: LFunctor k) => Term k (List Statement) -> Term k Statement
iBlock = inject . Block

iAssignment :: (StatementF :<: LFunctor k) => Term k Name -> Term k Expr -> Term k Statement
iAssignment x y = inject $ Assignment x y

iWhile :: (StatementF :<: LFunctor k) => Term k Expr -> Term k Statement -> Term k Statement
iWhile cond body = inject $ While cond body


instance (HEq h) => HEq (StatementF h) where
  {-# INLINABLE heq #-}
  heq (Declaration x)   (Declaration x')    = heq x x'
  heq (Block xs)        (Block xs')         = heq xs xs'
  heq (Assignment x y)  (Assignment x' y')  = heq x x' && heq y y'
  heq (While cond body) (While cond' body') = heq cond cond' && heq body body'
  heq _                 _                   = False


instance (HEq h) => HEqHet (StatementF h) where
  {-# INLINABLE heqIx #-}
  heqIx (Declaration _)  (Declaration _)  = Just Refl
  heqIx (Declaration _)  (Block _)        = Just Refl
  heqIx (Declaration _)  (Assignment _ _) = Just Refl
  heqIx (Declaration _)  (While _ _)      = Just Refl
  heqIx (Block _)        (Declaration _)  = Just Refl
  heqIx (Block _)        (Block _)        = Just Refl
  heqIx (Block _)        (Assignment _ _) = Just Refl
  heqIx (Block _)        (While _ _)      = Just Refl
  heqIx (Assignment _ _) (Declaration _)  = Just Refl
  heqIx (Assignment _ _) (Block _)        = Just Refl
  heqIx (Assignment _ _) (Assignment _ _) = Just Refl
  heqIx (Assignment _ _) (While _ _)      = Just Refl
  heqIx (While _ _)      (Declaration _)  = Just Refl
  heqIx (While _ _)      (Block _)        = Just Refl
  heqIx (While _ _)      (Assignment _ _) = Just Refl
  heqIx (While _ _)      (While _ _)      = Just Refl

instance (HOrd h) => HOrd (StatementF h) where
  {-# INLINABLE hcompare #-}
  hcompare (Declaration x)   (Declaration x')    = hcompare x x'
  hcompare (Declaration _)   _                   = LT
  hcompare (Block _)         (Declaration _)     = GT
  hcompare (Block x)         (Block x')          = hcompare x x'
  hcompare (Block _)         _                   = LT
  hcompare (Assignment _ _)  (Declaration _)     = GT
  hcompare (Assignment _ _)  (Block _)           = GT
  hcompare (Assignment x y)  (Assignment x' y')  = hcompare x x' <> hcompare y y'
  hcompare (Assignment _ _)  (While _ _)         = LT
  hcompare (While cond body) (While cond' body') = hcompare cond cond' <> hcompare body body'
  hcompare (While _ _)       _                   = GT

instance (HOrd h) => HOrdHet (StatementF h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx x y = {-# SCC hcompareIx_type_StatementF #-} go x y
    where
      go :: StatementF h ix -> StatementF h ix' -> HOrdering ix ix'
      go (Declaration _)  (Declaration _)  = HEQ
      go (Declaration _)  (Block _)        = HEQ
      go (Declaration _)  (Assignment _ _) = HEQ
      go (Declaration _)  (While _ _)      = HEQ
      go (Block _)        (Declaration _)  = HEQ
      go (Block _)        (Block _)        = HEQ
      go (Block _)        (Assignment _ _) = HEQ
      go (Block _)        (While _ _)      = HEQ
      go (Assignment _ _) (Declaration _)  = HEQ
      go (Assignment _ _) (Block _)        = HEQ
      go (Assignment _ _) (Assignment _ _) = HEQ
      go (Assignment _ _) (While _ _)      = HEQ
      go (While _ _)      (Declaration _)  = HEQ
      go (While _ _)      (Block _)        = HEQ
      go (While _ _)      (Assignment _ _) = HEQ
      go (While _ _)      (While _ _)      = HEQ

instance HFunctorId StatementF where
  hfmapId f (Declaration x)  = Declaration (f x)
  hfmapId f (Block xs)       = Block (f xs)
  hfmapId f (Assignment x y) = Assignment (f x) (f y)
  hfmapId f (While x y)      = While (f x) (f y)

instance HFoldable StatementF where
  hfoldMap f (Declaration x)  = f x
  hfoldMap f (Block xs)       = f xs
  hfoldMap f (Assignment x y) = f x <> f y
  hfoldMap f (While x y)      = f x <> f y

instance (HShow h) => HShow (StatementF h) where
  hshowsPrec n (Declaration name)  =
    showParen (n == 11) (showString "Declaration " . hshowsPrec 11 name)
  hshowsPrec n (Block xs)  =
    showParen (n == 11) (showString "Block " . hshowsPrec 11 xs)
  hshowsPrec n (Assignment name x) =
    showParen
      (n == 11)
      (showString "Assignment " . hshowsPrec 11 name . showString " " .
       hshowsPrec 11 x)
  hshowsPrec n (While cond body)   =
    showParen
      (n == 11)
      (showString "While " . hshowsPrec 11 cond . showString " " .
       hshowsPrec 11 body)

instance (HPretty h, ReifyList h h) => HPretty (StatementF h) where
  hpretty (Declaration name)  = "declare" <+> hpretty name
  hpretty (Block xs)          =
    case reifyList xs of
      []  -> lbrace <> rbrace
      xs' -> cbraces (PP.indent 2 (vsep $ map (\stmt -> hpretty stmt <> ";") xs'))
  hpretty (Assignment name x) = hpretty name <+> ":=" <+> hpretty x
  hpretty (While cond body) =
    "while" <+> parens (hpretty cond) <+> hpretty body

instance (Unifiable (LFunctor k) k, HFoldable (LFunctor k), HOrdHet (Term1 k), HOrdHet (Type (Term1 k)), LVar k) => Unifiable StatementF k where
  unify (Declaration x)   (Declaration x')    = unifyTerms x x'
  unify (Block xs)        (Block xs')         = unifyTerms xs xs'
  unify (Assignment x y)  (Assignment x' y')  = unifyTerms x x' >=> unifyTerms y y'
  unify (While cond body) (While cond' body') = unifyTerms cond cond' >=> unifyTerms body body'
  unify _                 _                   = const Nothing


instance (ix ~ Statement) => TypeI (StatementF h) ix where
  type SupportsIx (StatementF h) ix = Equal ix Statement
  data Type (StatementF h) idx where
    TStatement :: Type (StatementF h) Statement
  singType = TStatement

instance HEq (Type (StatementF h)) where
  {-# INLINABLE heq #-}
  heq TStatement TStatement = True

instance HEqHet (Type (StatementF h)) where
  {-# INLINABLE heqIx #-}
  heqIx TStatement TStatement = Just Refl

instance HOrd (Type (StatementF h)) where
  {-# INLINABLE hcompare #-}
  hcompare TStatement TStatement = EQ

instance HOrdHet (Type (StatementF h)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx TStatement TStatement = {-# SCC hcompareIx_type_StatementF #-} HEQ

-- Functions

data Function

data FunctionF h ix where
  Function :: h Name -> h (List Name) -> h Statement -> h Expr -> FunctionF h Function

iFunction
  :: (FunctionF :<: LFunctor k)
  => Term k Name
  -> Term k (List Name)
  -> Term k Statement
  -> Term k Expr
  -> Term k Function
iFunction name args body retExpr = inject $ Function name args body retExpr

instance (HEq h) => HEq (FunctionF h) where
  {-# INLINABLE heq #-}
  heq (Function x y z w) (Function x' y' z' w') =
    heq x x' && heq y y' && heq z z' && heq w w'

instance (HEq h) => HEqHet (FunctionF h) where
  {-# INLINABLE heqIx #-}
  heqIx (Function _ _ _ _) (Function _ _ _ _) = Just Refl

instance (HOrd h) => HOrd (FunctionF h) where
  {-# INLINABLE hcompare #-}
  hcompare (Function x y z w) (Function x' y' z' w') =
    hcompare x x' <> hcompare y y' <> hcompare z z' <> hcompare w w'

instance (HOrd h) => HOrdHet (FunctionF h) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx (Function _ _ _ _) (Function _ _ _ _) = {-# SCC hcompareIx_type_Function #-} HEQ


instance HFunctorId FunctionF where
  hfmapId f (Function x y z w) = Function (f x) (f y) (f z) (f w)

instance HFoldable FunctionF where
  hfoldMap f (Function x y z w) = f x <> f y <> f z <> f w

instance (HShow h) => HShow (FunctionF h) where
  hshowsPrec n (Function x y z w) =
    showParen
      (n == 11)
      (showString "Function " .
       hshowsPrec 11 x . showString " " .
       hshowsPrec 11 y . showString " " .
       hshowsPrec 11 z . showString " " .
       hshowsPrec 11 w)

instance (HPretty h, ReifyList h h) => HPretty (FunctionF h) where
  hpretty (Function name args body retExpr) =
    "function" <+> hpretty name <> parens (align (sep $ punctuate PP.comma $ map hpretty $ reifyList args)) <+>
    cbraces (hpretty body PP.<$> "return" <+> hpretty retExpr)

cbraces :: Doc -> Doc
cbraces x = lbrace PP.<$> PP.indent 2 x PP.<$> rbrace


instance (Unifiable (LFunctor k) k, HFoldable (LFunctor k), HOrdHet (Term1 k), HOrdHet (Type (Term1 k)), LVar k) => Unifiable FunctionF k where
  unify (Function name args body x) (Function name' args' body' y) =
    unifyTerms name name' >=>
    unifyTerms args args' >=>
    unifyTerms body body' >=>
    unifyTerms x y


instance (ix ~ Function) => TypeI (FunctionF h) ix where
  type SupportsIx (FunctionF h) ix = Equal ix Function
  data Type (FunctionF h) idx where
    TFunction :: Type (FunctionF h) Function
  singType = TFunction

instance HEq (Type (FunctionF h)) where
  {-# INLINABLE heq #-}
  heq TFunction TFunction = True

instance HEqHet (Type (FunctionF h)) where
  {-# INLINABLE heqIx #-}
  heqIx TFunction TFunction = Just Refl

instance HOrd (Type (FunctionF h)) where
  {-# INLINABLE hcompare #-}
  hcompare TFunction TFunction = EQ

instance HOrdHet (Type (FunctionF h)) where
  {-# INLINABLE hcompareIx #-}
  hcompareIx TFunction TFunction = {-# SCC hcompareIx_type_TFunction #-} HEQ

-- Main functor

type ProgramF   = ListF :+: NatF :+: NameF :+: ExprF :+: StatementF :+: FunctionF
type ProgramVar = Integer.LVar ProgramF
type Program    = Term ProgramVar
