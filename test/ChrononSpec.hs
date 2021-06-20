{-# LANGUAGE TupleSections #-}
module ChrononSpec where

import Data.Either
import Test.Hspec
import Chronon
import Unify
import Control.Monad.State.Lazy

lt :: Int -> Int -> Term
lt a b = app "lt" [var a, var b]

eq a b = app "=" [var a, var b]

emptySimpRule :: [Term] -> Rule
emptySimpRule terms = SimpRule "empty" (Head terms) (Body [])

propRule :: String -> [Term] -> [Term] -> Rule
propRule name terms body = PropRule name (Head terms) (Body body)
simpRule name terms body = SimpRule name (Head terms) (Body body)

spec :: Spec
spec = do
  describe "Eval" $ do
    it "should succeed" $ do
      let rules = [simpRule "reflective" [lt 1 2, lt 2 1] [eq 1 2], propRule "transitive" [lt 1 2, lt 2 3] [lt 1 3], simpRule "elimination" [eq 1 1] []]
      let cons = [lt 10 11, lt 11 12, lt 12 13, lt 13 10]
      let program = Program (map (, Active) cons)
      let history = History []
      evalStateT eval  (rules, program, history, nosub) `shouldReturn` Succeed 
      
