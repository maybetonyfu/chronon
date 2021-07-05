module ChrParser where

import Chr hiding (main)
import Control.Applicative ((*>), (<$), (<$>), (<*), (<*>))
import Control.Lens
import Control.Monad
import Control.Monad.Trans.State.Lazy
import Data.List
import Data.Maybe
import System.Environment
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.String (Parser, parseFromFile)

lexeme :: Parser a -> Parser a
lexeme p = p <* many (oneOf " \t")

data PTerm = PVar String | PCon String | PFun String [PTerm] deriving (Show)

data PRule
  = PPropRule String [PTerm] [PTerm]
  | PSimpRule String [PTerm] [PTerm]
  deriving (Show)

variable :: Parser PTerm
variable = do
  u <- upper
  v <- lexeme $ many alphaNum
  return $ PVar (u : v)

constant :: Parser PTerm
constant = do
  v <- many1 alphaNum
  return $ PCon v

function :: Parser PTerm
function = do
  fname <- many1 letter
  lexeme $ char '('
  terms <- sepBy term (lexeme $ char ',')
  lexeme $ char ')'
  return $ PFun fname terms

term :: Parser PTerm
term = variable <|> try function <|> constant

propRule :: Parser PRule
propRule = do
  ruleName <- lexeme $ many1 alphaNum
  lexeme $ char ':'
  heads <- lexeme $ sepBy term (lexeme $ char ',')
  lexeme $ string "==>"
  bodies <- lexeme $ sepBy term (lexeme $ char ',')
  return $ PPropRule ruleName heads bodies

simpRule :: Parser PRule
simpRule = do
  ruleName <- lexeme $ many1 alphaNum
  lexeme $ char ':'
  heads <- lexeme $ sepBy term (lexeme $ char ',')
  lexeme $ string "<=>"
  bodies <- lexeme $ sepBy term (lexeme $ char ',')
  return $ PSimpRule ruleName heads bodies

rule :: Parser PRule
rule = try propRule <|> simpRule

constraintProgram :: Parser [PTerm]
constraintProgram = sepEndBy term (many1 endOfLine)

chrProgram :: Parser [PRule]
chrProgram = sepEndBy rule (many1 endOfLine)

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
  es <- get
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
varSymbols (PCon c) = []
varSymbols (PFun name ts) = concatMap (nub . varSymbols) ts

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
        (Right chrs, Right cons) -> do
          putStrLn "Constraint handling rules:"
          mapM_ print chrs
          putStrLn "\nConstraints:"
          mapM_ print cons
          let state' =
                execState
                  (assemble chrs cons >> eval)
                  initState
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
    _ -> error "please pass one argument with the file containing the text to parse"
