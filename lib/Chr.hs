{-# LANGUAGE TemplateHaskell #-}

module Chr where

import Control.Lens
import Control.Monad
import Control.Monad.Trans.State.Lazy
import qualified Data.IntMap as IM
-- import qualified Data.IntSet as IS
import Data.List
import qualified Data.Map as Map
import Debug.Trace
import Graph

type Head = [Term]

type Body = [Term]

data Term = Var Int | Fun String [Term] deriving (Eq)

instance Ord Term where
  (Var x) <= (Var y) = x <= y
  (Var _) <= (Fun _ _) = True
  (Fun _ _) <= (Var _) = False
  (Fun name ts) <= (Fun name' ts') =
    case name `compare` name' of
      LT -> True
      GT -> False
      EQ -> case length ts `compare` length ts' of
        LT -> True
        GT -> False
        EQ -> case find (uncurry (/=)) (zip ts ts') of
          Just (a, b) -> a <= b
          Nothing -> True

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

isCon :: Term -> Bool
isCon (Fun _ []) = True
isCon _ = False

isFun :: Term -> Bool
isFun (Fun _ (x : _)) = True
isFun _ = False

author :: String
author = "Tony"

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM mcondition mthen melse = do
  condition <- mcondition
  if condition then mthen else melse

instance Show Term where
  show (Var n) = "v_" ++ show n
  show (Fun name []) = name
  show (Fun name terms) = name ++ "(" ++ (intercalate "," . map show $ terms) ++ ")"

showTerms :: [Term] -> String
showTerms [] = "Empty"
showTerms ts = intercalate "," . map show $ ts

isBuiltIn :: Term -> Bool
isBuiltIn (Fun "eq" [x, y]) = True
isBuiltIn (Fun "true" []) = True
isBuiltIn (Fun "false" []) = True
isBuiltIn (Fun "eq" xs) = error $ "Equality check should only have arity 2, encountered arity " ++ show (length xs)
isBuiltIn (Fun "true" _) = error "Constant 'true' cannot be used as a function"
isBuiltIn (Fun "false" _) = error "Constant 'false' cannot be used as a function"
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

type BuiltInStore = Graph Term

data EvalResult = RuleExausted | Unsatisfied UnifyResult | None deriving (Show, Eq)

data UnifyResult = UnifyOK | UnifyOccured | UnifyFailed | UnifyContradict deriving (Show, Eq)

isUnifySuccess :: UnifyResult -> Bool 
isUnifySuccess UnifyOK = True 
isUnifySuccess _ = False 

data EvalState = EvalState
  { _getNextVar :: Int,
    _symbolMap :: Map.Map String (Int, [String]),
    _getGoal :: Goal,
    _getUserStore :: UserStore,
    _getBuiltInStore :: BuiltInStore,
    _getLog :: [String],
    _getRules :: [Rule],
    _getMatchHistory :: [[Int]],
    _step :: Int,
    _skolemised :: [Term],
    _result :: EvalResult
  }
  deriving (Show)

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

registerVar :: Monad m => String -> [String] -> StateT EvalState m ()
registerVar symbol comments = do
  es <- get
  let v = view getNextVar es
  modify $ over getNextVar (+ 1) . over symbolMap (Map.insert symbol (v, comments))

lookupVar :: Monad m => String -> StateT EvalState m (Maybe Term)
lookupVar symbol = do
  es <- get
  case Map.lookup symbol (view symbolMap es) of
    Nothing -> return Nothing
    Just (t, _) -> return $ Just (Var t)

setVar :: Monad m => String -> [String] -> StateT EvalState m Term
setVar symbol comments = do
  inContext <- lookupVar symbol
  case inContext of
    Nothing -> registerVar symbol comments >> setVar symbol comments
    Just t -> return t

addSimpRule :: Monad m => String -> Head -> Body -> StateT EvalState m ()
addSimpRule name heads body = do
  es <- get
  let numberOfRules = length $ view getRules es
  modify $ over getRules (++ [SimpRule numberOfRules name heads body])

addPropRule :: Monad m => String -> Head -> Body -> StateT EvalState m ()
addPropRule name heads body = do
  es <- get
  let numberOfRules = length $ view getRules es
  modify $ over getRules (++ [PropRule numberOfRules name heads body])

substitute :: [(Term, Term)] -> Term -> Term
substitute unifier t@(Var _) =
  case find ((== t) . fst) unifier of
    Just (_, toVar) -> toVar
    Nothing -> t
substitute unifier (Fun name ts) = Fun name (map (substitute unifier) ts)

clone :: Monad m => Rule -> StateT EvalState m Rule
clone (SimpRule ruleId name heads bodies) = do
  let vars = nub . concatMap allVars $ (heads ++ bodies)
  unifier <- mapM 
    (\v -> do
        es <- get 
        let nextVarName = ('a':) . show . view getNextVar $  es
        v' <- setVar nextVarName ["Simplified from rule id=" ++ show ruleId]; return (v, v') 
      ) 
      vars
  return $ SimpRule ruleId name (map (substitute unifier) heads) (map (substitute unifier) bodies)
  where allVars (Var x) = [Var x]
        allVars (Fun _ ts) = concatMap allVars ts
clone (PropRule ruleId name heads bodies) = do
  let vars = nub . concatMap allVars $ (heads ++ bodies)
  unifier <- mapM 
    (\v -> do
        v' <- setVar ("a" ++ show v) ["Simplified from rule id=" ++ show ruleId]; return (v, v') 
      ) 
      vars
  return $ SimpRule ruleId name (map (substitute unifier) heads) (map (substitute unifier) bodies)
  where allVars (Var x) = [Var x]
        allVars (Fun _ ts) = concatMap allVars ts

deref :: Monad m => Int -> StateT EvalState m (Maybe Term)
deref n = do
  es <- get
  let buitInStore = view getBuiltInStore es
  let reached = Var n `reachable` buitInStore
  let skolemisedVars = view skolemised es
  return $ find (\t -> isFun t || isCon t || t `elem` skolemisedVars) reached

occur :: Monad m => Int -> Term -> StateT EvalState m Bool
occur n (Var m) =
  -- trace ("Occur Check var " ++ show m) $
  do
    rhs <- deref m
    case rhs of
      Nothing -> do
        es <- get
        let buitInStore = view getBuiltInStore es
        let reached = Var m `reachable` buitInStore
        return $ Var n `elem` reached
      Just (Var _) -> return False
      Just f@(Fun _ _) -> occur n f
occur n (Fun _ args) = do
  occured <- mapM (occur n) args
  return $ or occured

unify :: Monad m => Term -> Term -> StateT EvalState m UnifyResult
unify (Var x) (Var y) =
  -- trace ("Unify var " ++ show x ++ " and var " ++ show y) $
  do
    es <- get
    x' <- deref x
    y' <- deref y
    case (x', y') of
      (Just (Var sk1), Just (Var sk2)) -> return (if sk1 == sk2 then UnifyOK else UnifyFailed)
      (Just f1@(Fun _ _), Just f2@(Fun _ _)) -> unify f1 f2
      (Just f@(Fun _ _), _) -> unify (Var y) f
      (_, Just f@(Fun _ _)) -> unify (Var x) f
      (_, _) -> modify (over getBuiltInStore (addEdge (Var x) (Var y))) >> return UnifyOK
unify (Var x) f@(Fun _ _) =
  -- trace ("Unify var " ++ show x ++ " and fun " ++ show f) $
  do
    occured <- x `occur` f
    if occured
      then return UnifyOccured
      else do
        x' <- deref x
        case x' of
          Nothing -> modify (over getBuiltInStore (addEdge (Var x) f)) >> return UnifyOK
          Just (Var _) -> return UnifyFailed
          Just f'@(Fun _ _) -> unify f f'
unify (Fun name ts) (Var x) = unify (Var x) (Fun name ts)
unify (Fun name ts) (Fun name' ts') =
  -- trace ("Unify fun " ++ show (Fun name ts) ++ " and fun " ++ show (Fun name' ts')) $
  do
    case (name == name', length ts == length ts') of
      (True, True) -> do
        rs <- zipWithM unify ts ts'
        return $ if all (== UnifyOK) rs then UnifyOK else UnifyFailed
      _ -> return UnifyFailed

skolemise :: Monad m => Term -> StateT EvalState m ()
skolemise (Var x) =
  -- trace ( "Skolemise: Var " ++ show x) $
  do
    x' <- deref x
    case x' of
      Nothing -> modify $ over skolemised (Var x :)
      Just (Var _) -> return ()
      Just f@(Fun _ _) -> skolemise f
skolemise (Fun _ ts) =
  -- trace ( "Skolemise: Fun " ++ name) $
  do
    mapM_ skolemise ts

derive :: Monad m => Term -> StateT EvalState m Term
derive (Var x) =
  -- trace ( "Derive: Var " ++ show x) $
  do
    x' <- deref x
    case x' of
      Nothing -> return (Var x)
      Just (Var sk) -> return (Var sk)
      Just t@(Fun _ _) -> return t
derive (Fun name args) =
  -- trace ( "Derive: Fun " ++ show (Fun name args)) $
  do
    args' <- mapM derive args
    return (Fun name args')

appendLog :: Monad m => String -> StateT EvalState m ()
appendLog runLog = do
  es <- get
  let st = view step es
  let message = "[Step " ++ show st ++ "] " ++ runLog
  modify $ over getLog (++ [message])

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

solve :: Monad m => Term -> StateT EvalState m UnifyResult
solve t@(Fun _ [x, y]) =
  -- trace ("Solving " ++ show x ++ " = "  ++ show y) $
  do
    appendLog $ "Solve: " ++ show x ++ " = " ++ show y
    r <- unify x y
    if isUnifySuccess r
      then 
        do
          es <- get
          mapM_ activate (view getUserStore es)
          modify $ over getGoal (filter (/= t))
          return r
      else return r
solve t@(Fun "true" []) =
  -- trace "Solve: true" $
  do
    appendLog "Solve: True"
    modify $ over getGoal (filter (/= t))
    return UnifyOK
solve (Fun "false" []) =
  -- trace "Solve: false" $
  do
    appendLog "Solve: False"
    return UnifyContradict
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
activate uc =
  -- trace ("Active: " ++ show uc) $
  do
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
  let ruleId = getRuleId rule
  let headSize = length ruleHead
  let constraintGroups = permute headSize userStore
  let tries = map (zip ruleHead) constraintGroups
  hasMatch <-
    find isMatched
      <$> mapM
        ( \pairs -> do
            let matchedConstraint = map snd pairs
            let matchedTerms = map (view getTerm) matchedConstraint
            let matchHistory = ruleId : map (view getId . snd) pairs
            let isHistorical = matchHistory `elem` view getMatchHistory es
            -- this part reads: if all matching constraints for a PROPAGATION RULE are inactive, then it fails automatically
            -- if the matching combination has happened before, it fails automatically
            if ((not . any (view getActiveness)) matchedConstraint && isPropRule rule) || isHistorical
              then return Unmatch
              else do
                let vars = map (view getTerm . snd) pairs
                mapM_ skolemise vars -- For some reason, we need to force a strict evaluation on skolemise
                rs <- mapM (\(left, right) -> unify left (view getTerm right)) pairs
                put es
                newRule <- clone rule
                goal <- mapM derive (getRuleBody newRule)
                let newBuiltIn = zipWith (\ a b -> Fun "eq" [a, b]) matchedTerms (getRuleHead newRule)
                if all isUnifySuccess rs
                  then
                    return $
                      Matched
                        { _matchedRule = rule,
                          _matchedConstraints = matchedConstraint,
                          _newGoal = goal ++ newBuiltIn,
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
  r <- match rule
  case r of
    Unmatch -> matchRules rules
    m@Matched {} -> return m

eval :: Monad m => StateT EvalState m ()
eval = do
  modify $ over step (+ 1)
  es <- get
  let goal = view getGoal es
  if null goal
    then do
      r <- matchRules (view getRules es)
      case r of
        Unmatch -> modify (set result RuleExausted)
        Matched rule machedConstraints goal' historyEntry ->
          -- trace ("Rule matched" ++ show rule) $
          case rule of
            SimpRule {} ->
              -- trace ("Simplify: " ++ show machedConstraints) $
              do
                appendLog $ "Simplify: Rule=" ++ show (getRuleId rule) ++ ", Constraints: " ++ intercalate "," (map (show . view getId) machedConstraints)
                let removeMatchingHead = over getUserStore (map (\uc -> if uc `elem` machedConstraints then set getDeleted True uc else uc))
                modify $ over getMatchHistory (historyEntry :) . over getGoal (goal' ++) . removeMatchingHead
                mapM_ deactivate machedConstraints
                eval
            PropRule {} ->
              -- trace ("Propagate: " ++ show machedConstraints) $
              do
                appendLog $ "Propagate: Rule=" ++ show (getRuleId rule) ++ ", Constraints: " ++ intercalate "," (map (show . view getId) machedConstraints)
                modify $ over getMatchHistory (historyEntry :) . over getGoal (goal' ++)
                mapM_ deactivate machedConstraints
                eval
    else
      if isBuiltIn (head goal)
        then do
          r <- solve (head goal)
          if isUnifySuccess r then eval else modify (set result $ Unsatisfied r) 
        else introduce (head goal) >> eval

type ChrState = StateT EvalState

initState :: EvalState
initState =
  EvalState
    { _getNextVar = 100,
      _symbolMap = Map.empty,
      _getGoal = [],
      _getUserStore = [],
      _getBuiltInStore = emptyGraph,
      _getLog = [],
      _getRules = [],
      _getMatchHistory = [],
      _step = 0,
      _skolemised = [],
      _result = None
    }

main :: IO ()
main = do
  let lt x y = Fun "lt" [Var x, Var y]
  let eq x y = Fun "eq" [Var x, Var y]
  let state1 = initState
  let state' =
        execState
          ( addPropRule "transitive" [lt 0 1, lt 1 2] [lt 0 2]
              >> addSimpRule "reflection" [lt 0 1, lt 1 0] [eq 1 0]
              >> addSimpRule "antisymitry" [lt 0 0] []
              >> modify (set getGoal [lt 10 11, lt 11 12, lt 12 13, lt 13 14, lt 14 10])
              >> eval
          )
          state1

  let runLog = view getLog state'

  mapM_ putStrLn runLog
  putStrLn "\n----- Result -----"
  print (view result state')
  putStrLn "\n----- Rules -----"
  mapM_ print (view getRules state')
  putStrLn "\n----- Goals -----"
  putStrLn . showTerms $ view getGoal state'
  putStrLn "\n----- User Store -----"
  mapM_ print (view getUserStore state')
  putStrLn "\n----- Built-in Store -----"
  print (view getBuiltInStore state')
  putStrLn "\n----- Match history -----"
  mapM_ print (view getMatchHistory state')
