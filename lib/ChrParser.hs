module ChrParser where

import Chr hiding (main)
import Control.Applicative ((*>), (<$), (<$>), (<*), (<*>), (<|>))
import Control.Monad
import Data.List
import Data.Maybe
import Text.Parsec
  ( alphaNum,
    char,
    letter,
    many,
    many1,
    oneOf,
    parseTest,
    try,
    upper,
  )
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.String (Parser)

lexeme :: Parser a -> Parser a
lexeme p = p <* many (oneOf " \t")

data PTerm = PVar String | PCon String | PFun String [PTerm] deriving (Show)
data PRule =
      PPropRule String [PTerm] [PTerm]
    | PSimpRule String [PTerm] [PTerm] deriving Show

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
    ruleName <- lexeme $ many1 letter
    lexeme $ char ':'
    heads  <- lexeme $ sepBy term (lexeme $ char ',')
    lexeme $ string "==>"
    bodies <- lexeme $ sepBy term (lexeme $ char ',')
    return $ PPropRule ruleName heads bodies

simpRule :: Parser PRule
simpRule = do
    ruleName <- lexeme $ many1 letter
    lexeme $ char ':'
    heads  <- lexeme $ sepBy term (lexeme $ char ',')
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

main :: IO ()
main = do
    args <- getArgs
    case a of
      (a:b:_) -> do
        chrs <- parseFromFile (lexeme chrProgram) a
        constraints <- parseFromFile (lexeme constraintProgram) b
        case result of
          Left _ -> error "Parse error"
          Right t -> print $ eval (toCanonical t)
      _ -> error "please pass one argument with the file containing the text to parse"
