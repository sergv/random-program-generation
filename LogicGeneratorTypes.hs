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
import Language.HKanren.Types.List

import Text.PrettyPrint.Leijen.Text (Doc, (<+>), parens, group, align, lbrace, rbrace, punctuate, sep, vsep)
import qualified Text.PrettyPrint.Leijen.Text as PP

-- Names

data Name

-- newtype Name = Name Int
--   deriving (Show, Eq, Ord)
--
-- instance Pretty Name where
--   pretty (Name x) = PP.int x


data NameF :: (* -> *) -> (* -> *) where
  NameF :: Int -> NameF h Name

instance HEq (NameF h) where
  heq (NameF x) (NameF y) = x == y

instance HEqHet (NameF h) where
  heqIx (NameF _) (NameF _) = Just Refl

instance HOrd (NameF h) where
  hcompare (NameF x) (NameF y) = compare x y

instance HOrdHet (NameF h) where
  hcompareIx (NameF _) (NameF _) = HEQ Refl


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
  heq TName TName = True

instance HEqHet (Type (NameF h)) where
  heqIx TName TName = Just Refl

instance HOrd (Type (NameF h)) where
  hcompare TName TName = EQ

instance HOrdHet (Type (NameF h)) where
  hcompareIx TName TName = HEQ Refl

-- Expressions

data Expr

data ExprF h ix where
  Var     :: h Name -> ExprF h Expr
  Add     :: h Expr -> h Expr -> ExprF h Expr
  Mul     :: h Expr -> h Expr -> ExprF h Expr
  IsTrue  :: h Expr -> ExprF h Expr
  If      :: h Expr -> h Expr -> h Expr -> ExprF h Expr
  Funcall :: h Name -> h (List Expr) -> ExprF h Expr

deriving instance (Eq (h Expr), Eq (h Name), Eq (h (List Expr))) => (Eq (ExprF h ix))
deriving instance (Ord (h Expr), Ord (h Name), Ord (h (List Expr))) => (Ord (ExprF h ix))

instance (Eq (h Expr), Eq (h Name), Eq (h (List Expr))) => HEq (ExprF h) where
  heq = (==)

instance HEqHet (ExprF h) where
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

instance (Ord (h Expr), Ord (h Name), Ord (h (List Expr))) => HOrd (ExprF h) where
  hcompare = compare

instance HOrdHet (ExprF h) where
  hcompareIx (Var _) (Var _)       = HEQ Refl
  hcompareIx (Var _) (Add _ _)     = HGT
  hcompareIx (Var _) (Mul _ _)     = HGT
  hcompareIx (Var _) (IsTrue _)    = HGT
  hcompareIx (Var _) (If _ _ _)    = HGT
  hcompareIx (Var _) (Funcall _ _) = HGT

  hcompareIx (Add _ _) (Var _)       = HLT
  hcompareIx (Add _ _) (Add _ _)     = HEQ Refl
  hcompareIx (Add _ _) (Mul _ _)     = HGT
  hcompareIx (Add _ _) (IsTrue _)    = HGT
  hcompareIx (Add _ _) (If _ _ _)    = HGT
  hcompareIx (Add _ _) (Funcall _ _) = HGT

  hcompareIx (Mul _ _) (Var _)       = HLT
  hcompareIx (Mul _ _) (Add _ _)     = HLT
  hcompareIx (Mul _ _) (Mul _ _)     = HEQ Refl
  hcompareIx (Mul _ _) (IsTrue _)    = HGT
  hcompareIx (Mul _ _) (If _ _ _)    = HGT
  hcompareIx (Mul _ _) (Funcall _ _) = HGT

  hcompareIx (IsTrue _) (Var _)       = HLT
  hcompareIx (IsTrue _) (Add _ _)     = HLT
  hcompareIx (IsTrue _) (Mul _ _)     = HLT
  hcompareIx (IsTrue _) (IsTrue _)    = HEQ Refl
  hcompareIx (IsTrue _) (If _ _ _)    = HGT
  hcompareIx (IsTrue _) (Funcall _ _) = HGT

  hcompareIx (If _ _ _) (Var _)       = HLT
  hcompareIx (If _ _ _) (Add _ _)     = HLT
  hcompareIx (If _ _ _) (Mul _ _)     = HLT
  hcompareIx (If _ _ _) (IsTrue _)    = HLT
  hcompareIx (If _ _ _) (If _ _ _)    = HEQ Refl
  hcompareIx (If _ _ _) (Funcall _ _) = HGT

  hcompareIx (Funcall _ _) (Var _)       = HLT
  hcompareIx (Funcall _ _) (Add _ _)     = HLT
  hcompareIx (Funcall _ _) (Mul _ _)     = HLT
  hcompareIx (Funcall _ _) (IsTrue _)    = HLT
  hcompareIx (Funcall _ _) (If _ _ _)    = HLT
  hcompareIx (Funcall _ _) (Funcall _ _) = HEQ Refl


instance HFunctorId ExprF where
  hfmapId _ (Var x)        = Var x
  hfmapId g (Add x y)      = Add (g x) (g y)
  hfmapId g (Mul x y)      = Mul (g x) (g y)
  hfmapId g (IsTrue x)     = IsTrue (g x)
  hfmapId g (If c t f)     = If (g c) (g t) (g f)
  hfmapId g (Funcall f xs) = Funcall (g f) (g xs)

instance HFoldable ExprF where
  hfoldMap _ (Var _)        = mempty
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
  hpretty (IsTrue x)     = lbrace <> hpretty x <> rbrace
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


instance (Unifiable h h, HFoldable h, HOrdHet (h (Term h)), HOrdHet (Type (h (Term h)))) => Unifiable ExprF h where
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
  heq TExpr TExpr = True

instance HEqHet (Type (ExprF h)) where
  heqIx TExpr TExpr = Just Refl

instance HOrd (Type (ExprF h)) where
  hcompare TExpr TExpr = EQ

instance HOrdHet (Type (ExprF h)) where
  hcompareIx TExpr TExpr = HEQ Refl

-- Statements

data Statement

data StatementF h ix where
  Declaration :: h Name -> StatementF h Statement
  Assignment  :: h Name -> h Expr -> StatementF h Statement
  While       :: h Expr -> h (List Statement) -> StatementF h Statement

deriving instance (Eq (h Name), Eq (h (List Statement)), Eq (h Expr)) => Eq (StatementF h ix)
deriving instance (Ord (h Name), Ord (h (List Statement)), Ord (h Expr)) => Ord (StatementF h ix)


instance (Eq (h Name), Eq (h (List Statement)), Eq (h Expr)) => HEq (StatementF h) where
  heq = (==)

instance HEqHet (StatementF h) where
  heqIx (Declaration _)  (Declaration _)  = Just Refl
  heqIx (Declaration _)  (Assignment _ _) = Just Refl
  heqIx (Declaration _)  (While _ _)      = Just Refl
  heqIx (Assignment _ _) (Declaration _)  = Just Refl
  heqIx (Assignment _ _) (Assignment _ _) = Just Refl
  heqIx (Assignment _ _) (While _ _)      = Just Refl
  heqIx (While _ _)      (Declaration _)  = Just Refl
  heqIx (While _ _)      (Assignment _ _) = Just Refl
  heqIx (While _ _)      (While _ _)      = Just Refl

instance (Ord (h Name), Ord (h (List Statement)), Ord (h Expr)) => HOrd (StatementF h) where
  hcompare = compare

instance HOrdHet (StatementF h) where
  hcompareIx (Declaration _)  (Declaration _)  = HEQ Refl
  hcompareIx (Declaration _)  (Assignment _ _) = HGT
  hcompareIx (Declaration _)  (While _ _)      = HGT
  hcompareIx (Assignment _ _) (Declaration _)  = HLT
  hcompareIx (Assignment _ _) (Assignment _ _) = HEQ Refl
  hcompareIx (Assignment _ _) (While _ _)      = HGT
  hcompareIx (While _ _)      (Declaration _)  = HLT
  hcompareIx (While _ _)      (Assignment _ _) = HLT
  hcompareIx (While _ _)      (While _ _)      = HEQ Refl

instance HFunctorId StatementF where
  hfmapId f (Declaration x)  = Declaration (f x)
  hfmapId f (Assignment x y) = Assignment (f x) (f y)
  hfmapId f (While x y)      = While (f x) (f y)

instance HFoldable StatementF where
  hfoldMap f (Declaration x)  = f x
  hfoldMap f (Assignment x y) = f x <> f y
  hfoldMap f (While x y)      = f x <> f y

instance (HShow h) => HShow (StatementF h) where
  hshowsPrec n (Declaration name)  =
    showParen (n == 11) (showString "Declaration " . hshowsPrec 11 name)
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
  hpretty (Assignment name x) = hpretty name <+> ":=" <+> hpretty x
  hpretty (While cond body) =
    "while" <+> parens (hpretty cond) <+>
      cbraces (PP.indent 2 (vsep $ map (\stmt -> hpretty stmt <> ";") $ reifyList body))

instance (Unifiable h h, HFoldable h, HOrdHet (h (Term h)), HOrdHet (Type (h (Term h)))) => Unifiable StatementF h where
  unify (Declaration x)   (Declaration x')    = unifyTerms x x'
  unify (Assignment x y)  (Assignment x' y')  = unifyTerms x x' >=> unifyTerms y y'
  unify (While cond body) (While cond' body') = unifyTerms cond cond' >=> unifyTerms body body'
  unify _                 _                   = const Nothing


instance (ix ~ Statement) => TypeI (StatementF h) ix where
  type SupportsIx (StatementF h) ix = Equal ix Statement
  data Type (StatementF h) idx where
    TStatement :: Type (StatementF h) Statement
  singType = TStatement

instance HEq (Type (StatementF h)) where
  heq TStatement TStatement = True

instance HEqHet (Type (StatementF h)) where
  heqIx TStatement TStatement = Just Refl

instance HOrd (Type (StatementF h)) where
  hcompare TStatement TStatement = EQ

instance HOrdHet (Type (StatementF h)) where
  hcompareIx TStatement TStatement = HEQ Refl

-- Functions

data Function

data FunctionF h ix where
  Function :: h Name -> h (List Name) -> h (List Statement) -> h Expr -> FunctionF h Function

instance (HEq h) => HEq (FunctionF h) where
  heq (Function x y z w) (Function x' y' z' w') =
    heq x x' && heq y y' && heq z z' && heq w w'

instance HEqHet (FunctionF h) where
  heqIx (Function _ _ _ _) (Function _ _ _ _) = Just Refl

instance (HOrd h) => HOrd (FunctionF h) where
  hcompare (Function x y z w) (Function x' y' z' w') =
    hcompare x x' <> hcompare y y' <> hcompare z z' <> hcompare w w'

instance HOrdHet (FunctionF h) where
  hcompareIx (Function _ _ _ _) (Function _ _ _ _) = HEQ Refl


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
    "function" <+> hpretty name <> parens (sep $ punctuate PP.comma $ map hpretty $ reifyList args) <+>
    cbraces (PP.indent 2 $ vsep $ map hpretty (reifyList body) ++ ["return" <+> hpretty retExpr])

cbraces :: Doc -> Doc
cbraces x = lbrace PP.<$> PP.indent 2 x PP.<$> rbrace


instance (Unifiable h h, HFoldable h, HOrdHet (h (Term h)), HOrdHet (Type (h (Term h)))) => Unifiable FunctionF h where
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
  heq TFunction TFunction = True

instance HEqHet (Type (FunctionF h)) where
  heqIx TFunction TFunction = Just Refl

instance HOrd (Type (FunctionF h)) where
  hcompare TFunction TFunction = EQ

instance HOrdHet (Type (FunctionF h)) where
  hcompareIx TFunction TFunction = HEQ Refl

-- Main functor

type ProgramF = ListF :+: NameF :+: ExprF :+: StatementF :+: FunctionF
type Program = Term ProgramF
