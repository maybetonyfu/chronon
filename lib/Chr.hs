{-# LANGUAGE TemplateHaskell #-}

module Chr where

import Control.Lens
import Control.Monad
import Control.Monad.Trans.State.Lazy
import Data.Bifunctor
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.List
import Data.Maybe
import Debug.Trace

type Head = [Term]

type Body = [Term]

data Term = Var Int | Fun String [Term] deriving (Eq)

instance Show Term where
  show (Var n) = "v_" ++ show n
  show (Fun name []) = name
  show (Fun name terms) = name ++ "(" ++ (intercalate "," . map show $ terms) ++ ")"

allVars :: [Term] -> [Int]
allVars [] = []
allVars ((Var n) : ts) = let rest = allVars ts in if n `elem` rest then rest else n : rest
allVars ((Fun _ ts') : ts) = allVars (ts' ++ ts)

showTerms :: [Term] -> String
showTerms [] = "Empty"
showTerms ts = intercalate "," . map show $ ts

isBuiltIn :: Term -> Bool
isBuiltIn (Fun "eq" [x, y]) = True -- Currently only 'Equality' is in Consitraint theory
isBuiltIn (Fun "eq" xs) = error $ "Equality check should only have arity 2, encountered arity " ++ show (length xs)
isBuiltIn _ = False

data Rule
  = SimpRule Int String Head Body
  | PropRule Int String Head Body
  deriving (Eq)

isPropRule :: Rule -> Bool
isPropRule PropRule {} = True
isPropRule _ = False

isSimpRule :: Rule -> Bool
isSimpRule SimpRule {} = True
isSimpRule _ = False

getRuleId :: Rule -> Int
getRuleId (SimpRule ruleId _ _ _) = ruleId
getRuleId (PropRule ruleId _ _ _) = ruleId

getRuleHead :: Rule -> Head
getRuleHead (SimpRule _ _ heads _) = heads
getRuleHead (PropRule _ _ heads _) = heads

getRuleBody :: Rule -> Body
getRuleBody (SimpRule _ _ _ bodies) = bodies
getRuleBody (PropRule _ _ _ bodies) = bodies

getRuleName :: Rule -> String
getRuleName (SimpRule _ name _ _) = name
getRuleName (PropRule _ name _ _) = name

instance Show Rule where
  show (SimpRule ruleid name heads bodies) = show ruleid ++ "." ++ name ++ ":\t" ++ showTerms heads ++ " <=> " ++ showTerms bodies
  show (PropRule ruleid name heads bodies) = show ruleid ++ "." ++ name ++ ":\t" ++ showTerms heads ++ " ==> " ++ showTerms bodies

data Target = Aliased IS.IntSet | Bound Term | Skolemised Int deriving (Show, Eq)

data UserConstraint = UserConstraint
  { _getTerm :: Term,
    _getDeleted :: Bool,
    _getActiveness :: Bool,
    _getId :: Int
  }
  deriving (Show, Eq)

makeLenses ''UserConstraint

type Goal = [Term]

type UserStore = [UserConstraint]

type BuiltInStore = IM.IntMap Target

data EvalState = EvalState
  { _getNextVar :: Int,
    _getGoal :: Goal,
    _getUserStore :: UserStore,
    _getBuiltInStore :: BuiltInStore,
    _getLog :: [String],
    _getRules :: [Rule],
    _getMatchHistory :: [[Int]]
  }
  deriving (Show, Eq)

makeLenses ''EvalState

data MatchResult
  = Unmatch
  | Matched
      { _matchedRule :: Rule,
        _matchedConstraints :: [UserConstraint],
        _newGoal :: Goal,
        _history :: [Int]
      }
  deriving (Eq, Show)

makeLenses ''MatchResult

freshVar :: Monad m => StateT EvalState m Int
freshVar = do
  es <- get
  let v = view getNextVar es
  modify $ over getNextVar (+ 1)
  return v

addSimpRule :: Monad m => String -> Head -> Body -> StateT EvalState m ()
addSimpRule name head body = do
  es <- get
  let numberOfRules = length $ view getRules es
  modify $ over getRules (SimpRule numberOfRules name head body :)

addPropRule :: Monad m => String -> Head -> Body -> StateT EvalState m ()
addPropRule name head body = do
  es <- get
  let numberOfRules = length $ view getRules es
  modify $ over getRules (PropRule numberOfRules name head body :)

substitute :: [(Int, Int)] -> Term -> Term
substitute unifier (Var n) =
  case find ((== n) . fst) unifier of
    Just (from, to) -> Var to
    Nothing -> Var n
substitute unifier (Fun name ts) = Fun name (map (substitute unifier) ts)

deref :: Monad m => Int -> StateT EvalState m (Maybe Target)
deref n = do
  es <- get
  let buitInStore = view getBuiltInStore es
  return $ IM.lookup n buitInStore

ref :: Monad m => Int -> Target -> StateT EvalState m ()
ref n t = modify $ over getBuiltInStore (IM.insert n t)

occur :: Monad m => Int -> Term -> StateT EvalState m Bool
occur n (Var m) = do
  rhs <- deref m
  case rhs of
    Nothing -> return $ m == n
    Just (Bound t) -> occur n t
    Just (Aliased ms) -> return $ n `IS.member` ms
    Just (Skolemised m') -> return False
occur n (Fun _ args) = do
  occured <- mapM (occur n) args
  return $ or occured

unify :: Monad m => Term -> Term -> StateT EvalState m Bool
unify (Var x) (Var y) = do
  x' <- deref x
  y' <- deref y
  case (x', y') of
    (Nothing, Nothing) -> do
      let newAliases = IS.fromList [x, y]
      mapM_ (\n -> ref n (Aliased newAliases)) (IS.elems newAliases)
      return True
    (Nothing, Just (Aliased as)) -> do
      let newAliases = IS.insert x as
      mapM_ (\n -> ref n (Aliased newAliases)) (IS.elems newAliases)
      return True
    (Just (Aliased as), Nothing) -> do
      let newAliases = IS.insert y as
      mapM_ (\n -> ref n (Aliased newAliases)) (IS.elems newAliases)
      return True
    (Just (Aliased as), Just (Aliased bs)) -> do
      let newAliases = IS.union as bs
      mapM_ (\n -> ref n (Aliased newAliases)) (IS.elems newAliases)
      return True
    (Just (Skolemised sk1), Just (Skolemised sk2)) -> do
      return (sk1 == sk2)
    (Just (Skolemised sk1), Just (Aliased als)) -> do
      mapM_ (\n -> ref n (Skolemised sk1)) (IS.elems als)
      return True
    (Just (Aliased als), Just (Skolemised sk1)) -> do
      mapM_ (\n -> ref n (Skolemised sk1)) (IS.elems als)
      return True
    (Just (Skolemised sk1), Nothing) -> do
      ref y (Skolemised sk1)
      return True
    (Nothing, Just (Skolemised sk1)) -> do
      ref x (Skolemised sk1)
      return True
    (Just (Bound t), _) -> unify t (Var y)
    (_, Just (Bound t)) -> unify t (Var x)
unify (Var x) f@(Fun name ts) = do
  occured <- x `occur` f
  if occured
    then return False
    else do
      x' <- deref x
      case x' of
        Nothing -> ref x (Bound f) >> return True
        Just (Skolemised _) -> return False
        Just (Bound _) -> return False
        Just (Aliased vs) -> mapM_ (\v -> ref v (Bound f)) (IS.elems vs) >> return True
unify (Fun name ts) (Var x) = unify (Var x) (Fun name ts)
unify (Fun name ts) (Fun name' ts') = do
  case (name == name', length ts == length ts') of
    (True, True) -> do
      rs <- zipWithM unify ts ts'
      return $ all (== True) rs
    _ -> return False

skolemise :: Monad m => Int -> StateT EvalState m ()
skolemise x = do
  x' <- deref x
  case x' of
    Nothing -> ref x (Skolemised x)
    Just (Aliased as) -> mapM_ (\a -> ref a (Skolemised x)) (IS.elems as)
    Just (Skolemised sk) -> return ()
    Just (Bound _) -> error "Cannot skolemise a fun"

derive :: Monad m => Term -> StateT EvalState m Term
derive (Var x) = do
  x' <- deref x
  case x' of
    Nothing -> return (Var x)
    Just (Aliased as) -> return (Var x)
    Just (Skolemised sk) -> return (Var sk)
    Just (Bound t) -> return t
derive (Fun name args) = do
  args' <- mapM derive args
  return (Fun name args')

appendLog :: Monad m => String -> StateT EvalState m ()
appendLog log = modify $ over getLog (++ [log])

introduce :: Monad m => Term -> StateT EvalState m ()
introduce term =
  -- trace ("Introducing " ++ show term) $
  do
    appendLog $ "Introduce: " ++ show term
    es <- get
    -- It is important that we count every user constraint (INCLUDING the ones that are deleted)
    let nextConstraintId = length (view getUserStore es)
    case find ((== term) . view getTerm) (view getUserStore es) of
      Nothing -> modify $ over getGoal (filter (/= term)) . over getUserStore ([UserConstraint term False True nextConstraintId] ++)
      Just t -> modify $ over getGoal (filter (/= term))

solve :: Monad m => Term -> StateT EvalState m ()
solve t@(Fun _ [x, y]) = do
  appendLog $ "Solve: " ++ show x ++ " = " ++ show y
  unify x y
  es <- get
  mapM_ activate (view getUserStore es)
  modify $ over getGoal (filter (/= t))
solve _ = error "Cannot solve user constraint"

deactivate :: Monad m => UserConstraint -> StateT EvalState m ()
deactivate uc =
  -- trace ("Deactivating: " ++ show uc) $
  do
    es <- get
    let ucs = view getUserStore es
    let ucs' = map (\uc' -> if uc' == uc then set getActiveness False uc' else uc') ucs
    modify $ set getUserStore ucs'

activate :: Monad m => UserConstraint -> StateT EvalState m ()
activate uc = do
  es <- get
  let ucs = view getUserStore es
  let ucs' = map (\uc' -> if uc' == uc then set getActiveness True uc' else uc') ucs
  modify $ set getUserStore ucs'

permute :: Int -> [a] -> [[a]]
permute n = concatMap permutations . filter ((== n) . length) . subsequences

choose :: Int -> [a] -> [[a]]
choose n = filter ((== n) . length) . subsequences

match :: Monad m => Rule -> StateT EvalState m MatchResult
match rule = do
  -- This is the most computation heavy function
  es <- get
  let userStore = filter (not . view getDeleted) $ view getUserStore es
  let ruleHead = getRuleHead rule
  let ruleBody = getRuleBody rule
  let ruleId = getRuleId rule
  let headSize = length ruleHead
  let constraintGroups = permute headSize userStore
  let tries = map (zip ruleHead) constraintGroups
  hasMatch <-
    find isMatched
      <$> mapM
        ( \pairs -> do
            let matchedConstraint = map snd pairs
            let matchHistory = ruleId : map (view getId . snd) pairs
            let isHistorical = matchHistory `elem` view getMatchHistory es
            -- this part reads: if all matching constraints for a PROPAGATION RULE are inactive, then it fails automatically
            -- if the matching combination has happened before, it fails automatically
            if ((not . any (view getActiveness)) matchedConstraint && isPropRule rule) || isHistorical
              then return Unmatch
              else do
                let vars = allVars . map (view getTerm . snd) $ pairs
                mapM_ skolemise vars
                results <- mapM (\(left, right) -> unify left (view getTerm right)) pairs
                goal <- mapM derive ruleBody
                put es
                if and results
                  then
                    return $
                      Matched
                        { _matchedRule = rule,
                          _matchedConstraints = matchedConstraint,
                          _newGoal = goal,
                          _history = matchHistory
                        }
                  else return Unmatch
        )
        tries
  case hasMatch of
    Nothing -> return Unmatch -- match failed
    Just m -> return m

isMatched :: MatchResult -> Bool
isMatched Unmatch = False
isMatched _ = True

matchRules :: Monad m => [Rule] -> StateT EvalState m MatchResult
matchRules [] = return Unmatch
matchRules (rule : rules) = do
  result <- match rule
  case result of
    Unmatch -> matchRules rules
    m@Matched {} -> return m

eval :: Monad m => StateT EvalState m ()
eval = do
  es <- get
  let goal = view getGoal es
  if null goal
    then do
      result <- matchRules (view getRules es)
      case result of
        Unmatch -> appendLog "No rule can fire"
        Matched rule machedConstraints goal' history ->
          case rule of
            SimpRule {} ->
              -- trace ("History: " ++ show history ++ " Cons: " ++ showTerms goal') $
              do
                let removeMatchingHead = over getUserStore (map (\uc -> if uc `elem` machedConstraints then set getDeleted True uc else uc))
                modify $ over getMatchHistory (history :) . over getGoal (goal' ++) . removeMatchingHead
                mapM_ deactivate machedConstraints
                eval
            PropRule {} ->
              -- trace ("History: " ++ show history ++ " Cons: " ++ showTerms goal') $
              do
                modify $ over getMatchHistory (history :) . over getGoal (goal' ++)
                mapM_ deactivate machedConstraints
                eval
    else
      if isBuiltIn (head goal)
        then solve (head goal) >> eval
        else introduce (head goal) >> eval

main :: IO ()
main = do
  let lt x y = Fun "lt" [Var x, Var y]
  let eq x y = Fun "eq" [Var x, Var y]
  let state =
        EvalState
          { _getNextVar = 20,
            _getGoal =
              [ lt 10 11,
                lt 11 12,
                lt 12 13,
                lt 13 14,
                lt 14 10
              ],
            _getUserStore = [],
            _getBuiltInStore = IM.empty,
            _getLog = [],
            _getRules = [],
            _getMatchHistory = []
          }

  let state' =
        execState
          ( addPropRule "transitive" [lt 0 1, lt 1 2] [lt 0 2]
              >> addSimpRule "reflection" [lt 0 1, lt 1 0] [eq 1 0]
              >> addSimpRule "antisymitry" [lt 0 0] []
              >> eval
          )
          state

  let log = view getLog state'

  mapM_ putStrLn log
  putStrLn "\n----- Rules -----"
  mapM_ print (view getRules state')
  putStrLn "\n----- Goals -----"
  putStrLn . showTerms $ view getGoal state'
  putStrLn "\n----- User Store -----"
  mapM_ print (view getUserStore state')
  putStrLn "\n----- Built-in Store -----"
  mapM_ print (view getBuiltInStore state')
  putStrLn "\n----- Match history -----"
  mapM_ print (view getMatchHistory state')