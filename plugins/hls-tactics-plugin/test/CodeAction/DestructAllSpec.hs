{-# LANGUAGE OverloadedStrings #-}

module CodeAction.DestructAllSpec where

import Wingman.Types
import Test.Hspec
import Utils


spec :: Spec
spec = do
  let destructAllTest = goldenTest DestructGroup ""
  describe "provider" $ do
    mkTest
      "Requires args on lhs of ="
      "DestructAllProvider" 3 21
      [ (not, DestructGroup, "")
      ]
    mkTest
      "Can't be a non-top-hole"
      "DestructAllProvider" 8 19
      [ (not, DestructGroup, "")
      , (id, Destruct, "a")
      , (id, Destruct, "b")
      ]
    mkTest
      "Provides a destruct all otherwise"
      "DestructAllProvider" 12 22
      [ (id, DestructGroup, "")
      ]

  describe "golden" $ do
    destructAllTest 2 11 "DestructAllAnd"
    destructAllTest 4 23 "DestructAllMany"
    destructAllTest 2 18 "DestructAllNonVarTopMatch"
    destructAllTest 2 18 "DestructAllFunc"
    destructAllTest 19 18 "DestructAllGADTEvidence"
    destructAllTest  4 19 "DestructGroupPairCase"

