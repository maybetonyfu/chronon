module ChrononSpec where

import Data.Either
import Test.Hspec ( shouldSatisfy, it, describe, Spec )
import Chronon
import Unify

lt :: Int -> Int -> Term
lt a b = app "lt" [var a, var b]

emptySimpRule :: [Term] -> Rule
emptySimpRule terms = SimpRule (Head terms) (Body [])

propRule terms body = PropRule (Head terms) (Body body)
simpRule terms body = SimpRule (Head terms) (Body body)

spec :: Spec
spec = do
  describe "Matching" $ do
    it "should match lt(a,b) with lt(x,y)" $ do
        let rule = emptySimpRule [lt 1 2]
        let cons = [lt 3 4, lt 5 6]
        match rule cons `shouldSatisfy` isMatch
    it "should match lt(a,b), lt(b,c) with lt(y,z), lt(x,y)" $ do
        let rule = emptySimpRule [lt 1 2, lt 2 3]
        let cons = [lt 5 6, lt 4 5]
        match rule cons `shouldSatisfy` isMatch
    it "should not match lt(a,b), lt(b,c) with lt(x,y), lt(z,w)" $ do
        let rule = emptySimpRule [lt 1 2, lt 2 3]
        let cons = [lt 4 5, lt 6 7]
        match rule cons `shouldSatisfy` not . isMatch
  describe "Evaluating" $ do
    it "should eval lt(a,b),lt(b, c) <=> lt(a,c)" $ do
      let rule = propRule [lt 1 2, lt 2 3] [lt 1 3]
      let cons = [lt 10 11, lt 11 12]
      evalSmallStep [rule] cons `shouldSatisfy` (==3) . length
      
    it "should eval lt(a,b),lt(b, a) ==> []" $ do
      let rule = simpRule [lt 1 2, lt 2 1] []
      let cons = [lt 10 11, lt 11 10]
      evalSmallStep [rule] cons `shouldSatisfy` null

    it "should eval lt(a,b),lt(b, a) ==> [] (in reverse order)" $ do
      let rule = simpRule [lt 1 2, lt 2 1] []
      let cons = [lt 11 10, lt 10 11]
      evalSmallStep [rule] cons `shouldSatisfy` null