module Chronon where

import Control.Monad.State.Lazy
import Data.Either
import Data.List hiding (delete)
import Data.Maybe
import Debug.Trace
import Unify

author :: [Char]
author = "Tony"

data Rule
  = SimpRule Head Body
  | PropRule Head Body
  deriving (Show, Eq)

newtype Head = Head [Term] deriving (Show, Eq)
newtype Body = Body [Term] deriving (Show, Eq)
newtype Program = Program [(Term, ConstraintState)] deriving (Show)
data OpState = Marked | Deleted | Prepared | Ready deriving (Show)
data RuleState = Active Rule | Inactive deriving (Show)
data ConstraintState = CS OpState RuleState deriving (Show)

mark :: Term -> State Program ()
mark toMark = do
  (Program ps) <- get
  let ps' = map (\p@(term, CS os rs) -> if term == toMark then (term, CS Marked rs) else p) ps
  put (Program ps')

delete :: Term -> State Program ()
delete toDelete = do
  (Program ps) <- get
  let ps' = map (\p@(term, CS os rs) -> if term == toDelete then (term, CS Deleted rs) else p) ps
  put (Program ps')

prepare :: Term -> State Program ()
prepare toPrepare = do
  (Program ps) <- get
  put (Program $ (toPrepare, CS Prepared Inactive) : ps)

ready :: Term -> State Program ()
ready toReady = do
  (Program ps) <- get
  let ps' = map (\p@(term, CS os rs) -> if term == toReady then (term, CS Ready rs) else p) ps
  put (Program ps')

activate :: Term -> Rule -> State Program ()
activate toActivate rule = do
  (Program ps) <- get
  let ps' = map (\p@(term, CS os rs) -> if term == toActivate then (term, CS os (Active rule)) else p) ps
  put (Program ps')

deactivate :: Term -> State Program ()
deactivate toDeactive = do
  (Program ps) <- get
  let ps' = map (\p@(term, CS os rs) -> if term == toDeactive then (term, CS os Inactive) else p) ps
  put (Program ps')

getRuleHeads :: Rule -> [Term]
getRuleHeads (SimpRule (Head heads) _) = heads
getRuleHeads (PropRule (Head heads) _) = heads

data EvalState
  = CanNotEvaluate
  | Evaluated
      { matchedConstraints :: [Term],
        matchedRule :: Rule
      }
  deriving (Show)

data EvalResult = Success | Fail deriving (Show, Eq)

evalSmallStep :: [Rule] -> State Program EvalResult
evalSmallStep [] = return Fail
evalSmallStep (r : rs) = do
  (Program terms) <- get
  case match r (map fst terms) of
    Matched sub matchedTerms -> case r of
      SimpRule _ (Body bodies) -> do
        mapM_ (\(c, _) -> when (c `elem` matchedTerms) (mark c >> activate c r)) terms
        mapM_ (prepare . apply sub) bodies
        return Success
      PropRule _ (Body bodies) -> do
        mapM_ (\(c, _) -> when (c `elem` matchedTerms) (activate c r)) terms
        mapM_ (prepare . apply sub) bodies
        return Success
    Unmatched -> evalSmallStep rs

upkeep :: State Program ()
upkeep = do
  Program ps <- get
  mapM_
    ( \(c, CS opstate rulestate) ->
        case (opstate, rulestate) of
          (Marked, Active _) -> deactivate c >> delete c
          (Marked, Inactive) -> deactivate c
          (Prepared, Active _) -> deactivate c >> ready c
          (Prepared, Inactive) -> ready c
          (_, Active _) -> deactivate c
          _ -> return ()
    )
    ps

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
permute n = concatMap permutations . filter ((== n) . length) . subsequences

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
    go _ _ = Unmatched
