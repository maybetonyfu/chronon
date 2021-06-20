module Unify where

import Data.IntMap (IntMap, empty, insert, lookup)
import Prelude hiding (lookup)

data Term = TVar Int | TCon String | TApp String [Term] deriving (Show, Eq)

data Target = BoundCon Term | BoundApp Term | Aliased [Int] | Skolemised Int deriving (Show, Eq)

type Sub = IntMap Target

data UnifyError = Mismatch | Occured deriving (Eq, Show)

nosub :: IntMap Target
nosub = empty

var :: Int -> Term
var = TVar

con :: String -> Term
con = TCon

app :: String -> [Term] -> Term
app = TApp

target :: Int -> Sub -> Maybe Target
target = lookup

top :: Term
top = TCon "true"

bottom :: Term
bottom = TCon "false"

occur :: Term -> Term -> Sub -> Bool
occur (TVar x) (TVar v) subs =
  case target v subs of
    Nothing -> x == v
    Just (BoundCon _) -> False
    Just (BoundApp a) -> occur (TVar x) a subs
    Just (Aliased as) -> x `elem` as
occur (TVar x) (TCon c) subs = False
occur (TVar x) (TApp _ []) subs = False
occur (TVar x) (TApp name args) subs = any (\arg -> occur (TVar x) arg subs) args

unify :: Term -> Term -> Sub -> Either UnifyError Sub
unify (TCon a) (TCon b) subs = if a == b then Right subs else Left Mismatch
unify (TCon _) (TApp _ _) _ = Left Mismatch
unify (TApp _ _) (TCon _) _ = Left Mismatch
unify (TVar v) c@(TCon _) subs =
  case target v subs of
    Nothing -> Right $ insert v (BoundCon c) subs
    Just (Aliased as) -> Right $ foldr (\a s -> insert a (BoundCon c) s) subs as
    Just (BoundCon c') -> unify c c' subs
    Just (BoundApp _) -> Left Mismatch
    Just (Skolemised _) -> Left Mismatch
unify con@(TCon _) var@(TVar _) subs = unify var con subs
unify (TVar x) (TVar y) subs =
  case (target x subs, target y subs) of
    (Nothing, Nothing) ->
      let newAliases = if x == y then [x] else [x, y]
       in Right $ foldr (\a s -> insert a (Aliased newAliases) s) subs newAliases
    (Nothing, Just (Aliased as)) ->
      let newAliases = x : as
       in Right $ foldr (\a s -> insert a (Aliased newAliases) s) subs newAliases
    (Just (Aliased as), Nothing) ->
      let newAliases = y : as
       in Right $ foldr (\a s -> insert a (Aliased newAliases) s) subs newAliases
    (Just (Aliased as), Just (Aliased bs)) ->
      let newAliases = as ++ bs
       in Right $ foldr (\a s -> insert a (Aliased newAliases) s) subs newAliases
    (Nothing, Just (Skolemised n)) -> Right $ insert x (Skolemised n) subs
    (Just (Skolemised n), Nothing) -> Right $ insert y (Skolemised n) subs
    (Just (Aliased as), Just (Skolemised n)) -> Right $ foldr (\a s -> insert a (Skolemised n) s) subs as
    (Just (Skolemised n), Just (Aliased as)) -> Right $ foldr (\a s -> insert a (Skolemised n) s) subs as
    (Just (Skolemised n), Just (Skolemised m)) -> if m == n then Right subs else Left Mismatch
    (Just (BoundCon c), _) -> unify (TVar y) c subs
    (_, Just (BoundCon c)) -> unify (TVar x) c subs
    (Just (BoundApp a), _) -> unify (TVar y) a subs
    (_, Just (BoundApp a)) -> unify (TVar x) a subs
unify (TVar v) tapp@(TApp name args) subs =
  if occur (TVar v) tapp subs
    then Left Occured
    else case target v subs of
      Nothing -> Right $ insert v (BoundApp tapp) subs
      Just (BoundCon _) -> Left Mismatch
      Just (Skolemised _) -> Left Mismatch
      Just (BoundApp tapp') -> unify tapp tapp' subs
      Just (Aliased vs) -> Right $ foldr (\a s -> insert a (BoundApp tapp) s) subs vs
unify app@(TApp _ _) var@(TVar _) subs = unify var app subs
unify (TApp name1 args1) (TApp name2 args2) subs
  | name1 /= name2 = Left Mismatch
  | length args1 /= length args2 = Left Mismatch
  | otherwise = go args1 args2 subs
  where
    go [] [] subs = Right subs
    go (a1 : as1) (a2 : as2) subs =
      case unify a1 a2 subs of
        Left n -> Left n
        Right subs' -> go as1 as2 subs'

skolemise :: Term -> Sub -> Either UnifyError Sub
skolemise (TVar x) subs =
  case target x subs of
    Nothing -> Right $ insert x (Skolemised x) subs
    (Just (Aliased aliases)) -> Right $ foldr (\a s -> insert a (Skolemised x) s) subs aliases
    (Just (BoundCon _)) -> Left Mismatch
    (Just (BoundApp _)) -> Left Mismatch
    (Just (Skolemised y)) -> Right subs -- Should this be like this?
skolemise _ _ = Left Mismatch


varsIn :: Term -> [Term]
varsIn (TVar x) = [TVar x]
varsIn (TCon _) = []
varsIn (TApp _ args) = foldr (\t l -> varsIn t ++ l) [] args

apply :: Sub -> Term -> Term
apply subs (TCon x) = TCon x
apply subs (TApp name args) = TApp name (map (apply subs) args)
apply subs (TVar v) =
  case target v subs of
    Nothing  -> TVar v
    Just (Aliased _) -> TVar v
    Just (BoundCon c) -> c
    Just (BoundApp a) -> a
    Just (Skolemised v') -> TVar v'

