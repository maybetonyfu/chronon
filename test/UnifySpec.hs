module UnifySpec where

import Data.Either
import Test.Hspec
import Unify

spec :: Spec
spec = do
  describe "unify con and con" $ do
    it "should succeed if have same symbol" $ do
      ( Right nosub
          >>= unify (con "a") (con "a")
        )
        `shouldSatisfy` isRight
    it "should fail if symbols are different" $ do
      ( Right nosub
          >>= unify (con "a") (con "b")
        )
        `shouldBe` Left Mismatch

  describe "unify app and con" $ do
    it "should alwasy fail" $ do
      ( Right nosub
          >>= unify (con "a") (app "f" [])
        )
        `shouldBe` Left Mismatch

  describe "unify var and var" $ do
    it "should bind unbound var with unbound var" $ do
      ( Right nosub
          >>= unify (var 1) (var 2)
        )
        `shouldSatisfy` isRight
    it "should bind unbound var and con bound var" $ do
      ( Right nosub
          >>= unify (var 2) (con "a")
          >>= unify (var 1) (var 2)
        )
        `shouldSatisfy` isRight
    it "should bind unbound and app bound var" $ do
      ( Right nosub
          >>= unify (var 2) (app "f" [var 3, con "b"])
          >>= unify (var 1) (var 2)
        )
        `shouldSatisfy` isRight

    it "should fail to bind to skolemised vars" $ do
      ( Right nosub
          >>= skolemise (var 1)
          >>= skolemise (var 2)
          >>= unify (var 1) (var 2)
        )
        `shouldBe` Left Mismatch

  describe "unify var and con" $ do
    it "sholud bind unbound var with con" $ do
      ( Right nosub
          >>= unify (var 1) (con "a")
        )
        `shouldSatisfy` isRight
    it "should bind con-bound var with con (if it is the same symbol)" $ do
      ( Right nosub
          >>= unify (var 1) (con "a")
          >>= unify (var 1) (con "a")
        )
        `shouldSatisfy` isRight
    it "should fail to bind con-bound var with a different con" $ do
      ( Right nosub
          >>= unify (var 1) (con "b")
          >>= unify (var 1) (con "a")
        )
        `shouldBe` Left Mismatch
    it "should fail to bind con-bound var with a function" $ do
      ( Right nosub
          >>= unify (var 1) (app "f" [var 2, var 3])
          >>= unify (var 1) (con "a")
        )
        `shouldBe` Left Mismatch
    it "should bind all aliased vars" $ do
      ( Right nosub
          >>= unify (var 1) (var 2)
          >>= unify (var 1) (con "a")
        )
        `shouldSatisfy` isRight
    it "should fail to bind skolemise var and con" $ do
      ( Right nosub
          >>= skolemise (var 1)
          >>= unify (var 1) (con "a")
        )
        `shouldBe` Left Mismatch

  describe "unify var app" $ do
    it "shuold fail if var occured" $ do
      ( Right nosub
          >>= unify (var 1) (app "f" [var 1, var 2])
        )
        `shouldBe` Left Occured
    it "should fail if var occured indirectly" $ do
      ( Right nosub
          >>= unify (var 1) (var 2)
          >>= unify (var 1) (app "f" [var 2, var 3])
        )
        `shouldBe` Left Occured
    it "should fail to bind skolemised var and app" $ do
      ( Right nosub
          >>= skolemise (var 1)
          >>= unify (var 1) (app "f" [])
        )
        `shouldBe` Left Mismatch

  describe "unify app app" $ do
    it "should bind arg to arg" $ do
      ( Right nosub
          >>= unify (app "f" [var 1, var 2]) (app "f" [var 3, var 4])
        )
        `shouldSatisfy` isRight
    it "should bind succeed if args are already aliased" $ do
      ( Right nosub
          >>= unify (var 1) (var 3)
          >>= unify (var 2) (var 4)
          >>= unify (app "f" [var 1, var 2]) (app "f" [var 3, var 4])
        )
        `shouldSatisfy` isRight
    it "should fail if try to bind different functions" $ do
      ( Right nosub
          >>= unify (app "f" []) (app "g" [])
        )
        `shouldBe` Left Mismatch
    it "should fail if functions have different arity" $ do
      ( Right nosub
          >>= unify (app "f" [var 1, var 2]) (app "f" [var 3])
        )
        `shouldBe` Left Mismatch

  describe "apply substitution on a term" $ do
    it "should not change constant" $ do
      apply
        ( fromRight nosub $
            unify (var 1) (var 2) nosub
        )
        (con "a")
        `shouldBe` con "a"
    it "should not change unbound var" $ do
      apply
        ( fromRight nosub $
            unify (var 2) (con "a") nosub
        )
        (var 1)
        `shouldBe` var 1
    it "should not change aliased var" $ do
      apply
        ( fromRight nosub $
            unify (var 1) (var 2) nosub
        )
        (var 1)
        `shouldBe` var 1
    it "should apply con bound var" $ do
      apply
        ( fromRight nosub $
            unify (var 1) (con "a") nosub
        )
        (var 1)
        `shouldBe` con "a"
    it "should apply app bound var" $ do
      apply
        ( fromRight nosub $
            unify (var 1) (app "+" []) nosub
        )
        (var 1)
        `shouldBe` app "+" []
    it "should apply skolemised var" $ do
      apply
        ( fromRight nosub $
            Right nosub
              >>= unify (var 1) (var 2)
              >>= skolemise (var 2)
        )
        (var 1)
        `shouldBe` var 2
