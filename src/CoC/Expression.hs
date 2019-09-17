{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

module CoC.Expression where

import Data.Text (Text)
import Data.Set (Set, singleton, delete)
import Data.Map (Map, lookup, insert, mapKeysMonotonic)
import qualified Data.Map as M
import Prelude hiding (lookup)
import Data.Foldable

type ParsedType a = ParsedTerm a

data ParsedTerm a =
    VarP a
  | AnnP a (ParsedType a)
  | LamP a (Term a)
  | AppP (Term a) (Term a)
  | PiP a (Term a) (Term a)
  | LetP a (Term a) (Term a)
  | LetRecP a (Term a) (Term a)
  | FixP a (Term a)


data Level = Z | S Level
  deriving (Eq)

levelToInt :: Level -> Int
levelToInt Z = 0
levelToInt (S l) = (+ 1) (levelToInt l)

instance Show Level where
  show = show . levelToInt

data Sort = Type Level
  deriving (Eq)

instance Show Sort where
  show (Type Z) = "*"
  show (Type l) = "Type_" <> show l


data Term a =
    Kind Sort
  | Var a
  | App (Term a) (Term a)
  | Lam a (Term a) (Term a)
  | Pi a (Term a) (Term a)
  deriving (Functor)

type Program a = [Block Term a]
data Block l a  = Block
  { identifier :: a
  , blockTerm  :: l a
  }

-- Note: This might be changed to something actually useful, who is to say.
type Scope f a = f a

data Var a = B Int | F a
  deriving (Eq)

var :: a -> Var a
var = F


freeVars :: (Ord a) => Term a -> Set a
freeVars (Kind _)         = mempty
freeVars (Var a)          = singleton a
freeVars (App l r)        = freeVars l <> freeVars r
freeVars (Lam nm ty expr) = freeVars ty <> nm `delete` freeVars expr
freeVars (Pi nm kd expr)  = freeVars kd <> nm `delete` freeVars expr


toLocallyNameless :: forall a . (Ord a) => Term a -> Term (Var a)
toLocallyNameless = go mempty
  where
    go :: Map a Int -> Term a -> Term (Var a)
    go env = \case
      Kind k1    -> Kind k1
      v@(Var a)  ->
        case a `lookup` env of
          Just bv -> Var (B bv)
          Nothing -> Var (F a)
      a@(App l r) -> App (go env l) (go env r)
      Lam n t e   ->
        let
          env' = insert n 0 (M.map (+ 1) env)
        in
          Lam (var n) (go env' t) (go env' e)
      Pi n t e    ->
        let
          env' = insert n 0 (M.map (+ 1) env)
        in
          Pi (var n) (go env' t) (go env' e)


fromLocallyNameless :: forall a . (Ord a) => Term (Var a) -> Term a
fromLocallyNameless = go mempty
  where
    go :: Map Int a -> Term (Var a) -> Term a
    go env = \case
      Kind k1 -> Kind k1
      Var v ->
        case v of
          F a  -> Var a
          B bv -> case bv `lookup` env of
            Just name -> Var name
            Nothing   -> error $ "Found bound variable with binding:" <> (show bv)
      App l r -> App (go env l) (go env r)
      Lam n t e ->
        case n of
          B bv -> error $ "Found unnamed variable at binding site" <> (show bv)
          F v  ->
            let
              env' = insert 0 v (mapKeysMonotonic (+ 1) env)
            in
              Lam v (go env' t) (go env' e)
      Pi n t e ->
        case n of
          B bv -> error $ "Found unnamed variable at binding site" <> (show bv)
          F v  ->
            let
              env' = insert 0 v (mapKeysMonotonic (+ 1) env)
            in
              Pi v (go env' t) (go env' e)

-- |
-- Open takes a term with an outer binder and instantiates that binder
-- with a given term. If this term is a variable then this is the usual
-- open operator.
open :: forall a . Term (Var a) -> Scope Term (Var a) -> Term (Var a)
open image = go 0
  where
    go :: Int -> Term (Var a) -> Term (Var a)
    go outer =
      \case
        Kind k1 -> Kind k1
        Var v ->
          case v of
            B bv | bv == outer -> image
                 | otherwise -> Var (B bv)
            F v -> Var (F v)
        App l r -> App (go outer l) (go outer r)
        Lam n t b -> Lam n (go (outer + 1) t) (go (outer + 1) b)
        Pi n t b -> Pi n (go (outer + 1) t) (go (outer + 1) b)

  -- To do: add open for a collection of variables
-- |
-- Close takes a term and a given free variable and converts that to an
-- outer binder. This can be uses to abstract a variable.

  -- To do : use this in the converstion to LN
close :: a -> Term (Var a) -> Scope Term (Var a)
close = undefined


-- |
-- substitute is just a convenient short-hand for open.
substitute :: Term (Var a) -> Scope Term (Var a) -> Term (Var a)
substitute = open


whnfLN :: Term (Var a) -> Term (Var a)
whnfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (# t, as #) of
        (# (App l r), args #)
          -> go l (r : args )
        (# (Lam _ _ body) , a:args #)
          -> go (substitute a body) args
        (# lam, args #)
          -> foldl' App lam as          


whnf :: (Ord a) => Term a -> Term a
whnf = fromLocallyNameless . whnfLN . toLocallyNameless


-- |
-- Reduce to normal form using a [WHAT] strategy.
nfLN :: Term (Var a) -> Term (Var a)
nfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (# t, as #) of
        (# (App l r), args #)
          -> go l (r : args)
        (# (Lam _ _ body) , a:args #)
          -> go (substitute a body) args
        (# lam, args #)
          -> foldl' App lam (fmap nfLN as)


nf :: (Ord a) => Term a -> Term a
nf = fromLocallyNameless . nfLN . toLocallyNameless


         
          
    
  
        
        
         
        
      
      

      
      


