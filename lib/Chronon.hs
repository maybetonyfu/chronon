{-# LANGUAGE TupleSections #-}

module Chronon where

import Control.Monad.Trans.State.Lazy
import Data.Either
import Data.List hiding (delete)
import Data.Maybe
import Debug.Trace
import Unify
import Control.Applicative.Lift
author :: [Char]
author = "Tony"

data Rule
  = SimpRule String Head Body
  | PropRule String Head Body
  deriving (Show, Eq)

ruleName :: Rule -> String
ruleName (SimpRule name _ _) = name
ruleName (PropRule name _ _) = name

isSimpRule :: Rule -> Bool
isSimpRule SimpRule {} = True
isSimpRule _ = False

isPropRule :: Rule -> Bool
isPropRule PropRule {} = True
isPropRule _ = False

getRuleHeads :: Rule -> [Term]
getRuleHeads (SimpRule _ (Head heads) _) = heads
getRuleHeads (PropRule _ (Head heads) _) = heads

getRuleBodies :: Rule -> [Term]
getRuleBodies (SimpRule _ _ (Body bodies)) = bodies
getRuleBodies (PropRule _ _ (Body bodies)) = bodies

newtype Head = Head [Term] deriving (Show, Eq)

newtype Body = Body [Term] deriving (Show, Eq)

data Status = Active | Passive deriving (Show, Eq)

newtype Program = Program [(Term, Status)] deriving (Show, Eq)

newtype History = History [Step] deriving (Show, Eq)

isInHistory :: History -> Rule -> [Term] -> Bool
isInHistory (History []) _ _ = False
isInHistory (History (step : steps)) rule terms =
  if matchedRule step == rule && all (`elem` terms) (matcedConstraints step)
    then True
    else isInHistory (History steps) rule terms

data Step
  = Step
      { matchedRule :: Rule,
        matcedConstraints :: [Term],
        toAdd :: [Term],
        toDelete :: [Term],
        toDeactivate :: [Term]
      }
  | NoMatch
  deriving (Show, Eq)

data Answer = FailNoRuleApply | Succeed deriving (Show, Eq)

type CHRState = StateT ([Rule], Program, History, Sub)

add :: Monad m => [Term] -> CHRState m ()
add [] = return ()
add (t : ts) = do
  (r, Program ps, h, u) <- get
  let allConstraint = map fst ps
  let newProgram = Program $
                    if t `elem` allConstraint
                      then ps
                      else map (,Active) (t : allConstraint)
  case t of
    TApp "=" (x : y : _) ->
      case unify x y u of
        Right u' -> do 
          put (r, newProgram, h, u') >> add ts
        Left _ -> do 
          put (r, newProgram, h, u)>> add ts
    _ -> do 
      put (r, newProgram, h, u) >> add ts

delete :: Monad m => [Term] -> CHRState m ()
delete ts = do
  (r, Program ps, h, u) <- get
  let newProgram = Program (filter ((`notElem` ts) . fst) ps)
  put (r, newProgram, h, u)

deactivate :: Monad m => [Term] -> CHRState m ()
deactivate ts = do
  (r, Program ps, h, u) <- get
  let newProgram = Program (map (\(t, s) -> if t `elem` ts then (t, Passive) else (t, s)) ps)
  put (r, newProgram, h, u)

commit :: Monad m => Step -> CHRState m ()
commit step = do
  add (toAdd step)
  delete (toDelete step)
  deactivate (toDeactivate step)
  modify (\(r, p, History h, u) -> (r, p, History (step : h), u))

eval :: CHRState IO Answer
eval = do
  (_, Program ps, _, u) <- get
  if null ps 
    then return Succeed
    else do 
      matched <- headMatching
      case matched of
        NoMatch -> return FailNoRuleApply
        step -> do
          commit step
          eval

headMatching :: Monad m => CHRState m Step
headMatching = do
  (rules, Program ps, _, u) <- get
  let currentConstraint = find ((== Active) . snd) ps
  let restOfConstraints = filter
  case currentConstraint of
    Just (term, status) -> do
      let restOfConstraints = filter (/= term) . map fst $ ps
      isMatch <- matchRules term restOfConstraints rules
      case isMatch of
        NoMatch -> deactivate [term] >> headMatching
        step -> return step
    Nothing -> return NoMatch

matchRules :: Monad m => Term -> [Term] -> [Rule] -> CHRState m Step
matchRules c cs [] = return NoMatch
matchRules c cs (r : rs) = do
  isMatch <- matchRule c cs r
  case isMatch of
    NoMatch -> matchRules c cs rs
    step -> return step

matchRule :: Monad m => Term -> [Term] -> Rule -> CHRState m Step
matchRule c cs rule = do
  (_, _, h, u) <- get
  let heads = getRuleHeads rule
      bodies = getRuleBodies rule
      numOfHeads = length heads
      permuted = concatMap (permutations . (c :)) . filter ((== numOfHeads - 1) . length) . subsequences $ cs
      allVals = concatMap varsIn (c : cs)
      initailSub = foldr (\t sub -> fromRight nosub (skolemise t sub)) u allVals
      go :: [Term] -> [Term] -> [Term] -> State Sub [Term]
      go [] [] matched = return matched
      go (h : hs) (con : cons) matched = do
        sub <- get
        case unify h con sub of
          Right sub' -> put sub' >> go hs cons (con : matched)
          Left _ -> return []
      go _ _ _ = error ""
      results = map (\cs' -> runState (go heads cs' []) initailSub) permuted
      notInHistory = filter (\(terms, _) -> not (isInHistory h rule terms))
      maybeMatch = find ((not . null) . fst) (notInHistory results)
  case maybeMatch of
    Nothing -> return NoMatch
    Just (terms, sub) ->
      return
        Step
          { matchedRule = rule,
            matcedConstraints = terms,
            toAdd = map (apply sub) bodies,
            toDelete = if isSimpRule rule then terms else [],
            toDeactivate = [c | not (isSimpRule rule)]
          }