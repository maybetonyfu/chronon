module Chronon where

import Data.Either
import Data.List
import Data.Maybe
import Unify
import Debug.Trace
import Control.Monad.State.Lazy

author :: [Char]
author = "Tony"

data Rule
  = SimpRule Head Body
  | PropRule Head Body
  deriving (Show, Eq)

newtype Head = Head [Term] deriving (Show, Eq)
newtype Body = Body [Term] deriving (Show, Eq)

data Program = Program [(Term, Bool)] deriving Show
data EliminateState = Marked | Deleted
data IntroduceState = Planned 
data RuleState = Active Rule | Inactive


getRuleHeads :: Rule -> [Term]
getRuleHeads (SimpRule (Head heads) _) = heads
getRuleHeads (PropRule (Head heads) _) = heads

data EvalState = CanNotEvaluate | Evaluated {
  matchedConstraints:: [Term],
  matchedRule:: Rule
} deriving Show
data EvalResult = Success | Fail

evalSmallStep :: [Rule] -> State Program ()
evalSmallStep [] = return ()
evalSmallStep (r : rs) = do 
  (Program terms) <- get
  case match r (map fst terms) of
    Matched sub matchedTerms -> case r of
      SimpRule _ (Body bodies) -> do
        let oldTerms = map (\(c, b) -> if c `elem` matchedTerms then (c, True) else (c, False)) terms
        let newTerms = map (\body -> (apply sub body, False)) bodies
        put $ Program (oldTerms ++ newTerms)
      PropRule _ (Body bodies) -> do
        let newTerms = map (\body -> (apply sub body, False)) bodies
        put $ Program (terms ++ newTerms)
    Unmatched -> evalSmallStep rs

-- eval :: [Rule] -> Program -> EvalResult
-- eval rules p =
--   case evalSmallStep rules p of
--     CanNotEvaluate -> undefined 
--     Evaluated newTerms -> 
--       if bottom `elem` newTerms
--         then Fail
--         else 
--           if null newTerms 
--             then Success
--             else eval rules newTerms 

data MatchResult
  = Matched Sub [Term]
  | Unmatched
  deriving (Show)

isMatch :: MatchResult -> Bool
isMatch (Matched _ _) = True
isMatch _ = False

permute :: Int -> [a] -> [[a]]
permute n = concatMap permutations . filter ((==n) . length) . subsequences

match :: Rule -> [Term] -> MatchResult
match rule constraints =
  fromMaybe
    Unmatched
    (find isMatch $ map (go heads) initailResults)
  where
    heads = getRuleHeads rule
    permuted = permute (length heads) constraints
    allVals = concatMap varsIn constraints
    initailSub = foldr (\t sub -> fromRight nosub (skolemise t sub)) nosub allVals
    initailResults = map (Matched initailSub) permuted
    go :: [Term] -> MatchResult -> MatchResult
    go [] r = r
    go (h : hs) (Matched sub (c : cs)) =
      case unify h c sub of
        Right sub' -> go hs (Matched sub' (cs ++ [c]))
        Left _ -> Unmatched
