module ChrSpec where

import Data.Either
import Test.Hspec

spec :: Spec
spec = do
  describe "Something" $ do
    it "should do something" $ do
      1 `shouldBe` 1