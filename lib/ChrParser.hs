module ChrParser where

import Chr hiding (main)
import Control.Lens
import Control.Monad.Trans.State.Lazy
import qualified Data.IntMap as IM
import qualified Data.Set as Set
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import System.Environment
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.String
import Graph
import Control.Monad

lexeme :: Parser a -> Parser a
lexeme p = p <* many (oneOf " \t")

data PTerm = PVar String | PCon String | PFun String [PTerm] deriving (Show)

data PRule
  = PPropRule String [PTerm] [PTerm]
  | PSimpRule String [PTerm] [PTerm]
  deriving (Show)

identifier :: Parser Char
identifier = alphaNum <|> char '_'

variable :: Parser PTerm
variable = do
  u <- upper
  v <- many identifier
  return $ PVar (u : v)

constant :: Parser PTerm
constant = do
  u <- lower
  v <- many identifier
  return $ PCon (u : v)

function :: Parser PTerm
function = do
  fname <- lexeme $ many1 identifier
  void . lexeme $ char '('
  terms <- sepBy term (lexeme $ char ',')
  void . lexeme $ char ')'
  return $ PFun fname terms

comment :: Parser ()
comment = do 
  void . lexeme $ string "--"
  void $ many anyChar 


term :: Parser PTerm
term = variable <|> try function <|> constant

propRule :: Parser PRule
propRule = do
  ruleName <- lexeme $ many1 identifier
  void . lexeme $ char ':'
  heads <- lexeme $ sepBy term (lexeme $ char ',')
  void . lexeme $ string "==>"
  bodies <- lexeme $ sepBy term (lexeme $ char ',')
  return $ PPropRule ruleName heads bodies

simpRule :: Parser PRule
simpRule = do
  ruleName <- lexeme $ many1 identifier
  void . lexeme $ char ':'
  heads <- lexeme $ sepBy term (lexeme $ char ',')
  void . lexeme $ string "<=>"
  bodies <- lexeme $ sepBy term (lexeme $ char ',')
  return $ PSimpRule ruleName heads bodies

rule :: Parser PRule
rule = try propRule <|> simpRule

newlineOrComment :: Parser ()
newlineOrComment = void endOfLine <|> comment

constraintProgram :: Parser [PTerm]
constraintProgram = sepEndBy term (many1 newlineOrComment)

chrProgram :: Parser [PRule]
chrProgram = sepEndBy rule (many1 newlineOrComment)

test :: IO ()
test = do
  parseTest term "true"
  parseTest term "X0  "
  parseTest term "X1"
  parseTest term "max(1)"
  parseTest term "f(X1, X2)"
  parseTest term "f(X1, g(Y, true))"
  parseTest rule "a: f(X) ==> g(X) "
  parseTest rule "a: f(X) <=> false "

assemble :: Monad m => [PRule] -> [PTerm] -> ChrState m ()
assemble parsedRules parsedTerms = do
  let symbolMapLocal = concatMap (nub . ruleSymbols) parsedRules
  mapM_
    ( \prule -> do
        case prule of
          PSimpRule name heads bodies -> addSimpRule name (map (ptermToLocalTerm symbolMapLocal) heads) (map (ptermToLocalTerm symbolMapLocal) bodies)
          PPropRule name heads bodies -> addPropRule name (map (ptermToLocalTerm symbolMapLocal) heads) (map (ptermToLocalTerm symbolMapLocal) bodies)
    )
    parsedRules
  modify $ set getNextVar (length symbolMapLocal)
  goals <- mapM ptermToTerm parsedTerms
  modify $ set getGoal goals

ptermToTerm :: Monad m => PTerm -> ChrState m Term
ptermToTerm (PVar v) = setVar v []
ptermToTerm (PCon c) = return $ Fun c []
ptermToTerm (PFun name args) = Fun name <$> mapM ptermToTerm args

ptermToLocalTerm :: [String] -> PTerm -> Term
ptermToLocalTerm symbols (PVar v) = Var (fromJust (elemIndex v symbols))
ptermToLocalTerm _ (PCon c) = Fun c []
ptermToLocalTerm symbols (PFun name args) = Fun name (map (ptermToLocalTerm symbols) args)

varSymbols :: PTerm -> [String] -- THis is purely LOCAL symbol map, just for symbols in rules
varSymbols (PVar v) = [v]
varSymbols (PCon _) = []
varSymbols (PFun _ ts) = concatMap (nub . varSymbols) ts

ruleSymbols :: PRule -> [String]
ruleSymbols (PSimpRule _ heads bodies) = concatMap (nub . varSymbols) (heads ++ bodies)
ruleSymbols (PPropRule _ heads bodies) = concatMap (nub . varSymbols) (heads ++ bodies)

main :: IO ()
main = do
  args <- getArgs
  case args of
    (a : b : _) -> do
      chrResult <- parseFromFile (lexeme chrProgram) a
      constraintResult <- parseFromFile (lexeme constraintProgram) b
      case (chrResult, constraintResult) of
        (Left e, _) -> error $ show e
        (_, Left e) -> error $ show e
        (Right chrs, Right constraints) -> do
          putStrLn "Constraint handling rules:"
          mapM_ print chrs
          putStrLn "\nConstraints:"
          mapM_ print constraints
          let state' =
                execState
                  (assemble chrs constraints >> eval)
                  initState
          inspectEvalState state'
    _ -> error "please pass one argument with the file containing the text to parse"
