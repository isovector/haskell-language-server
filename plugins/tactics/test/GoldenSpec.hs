module GoldenSpec where

import Machinery
import Test.Hspec
import Control.Monad.IO.Class


spec :: Spec
spec =
  describe "golden" $ do
    it "can typecheck things" $ do
      _x <- liftIO $ typecheck "fmap_list.hs"
      True `shouldBe` True


