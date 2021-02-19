{-# LANGUAGE OverloadedStrings #-}

module Copilot.TestTypes where

import qualified Data.Text as T
import Data.Aeson
import Copilot.FeatureSet

------------------------------------------------------------------------------
-- | The list of tactics exposed to the outside world. These are attached to
-- actual tactics via 'commandTactic' and are contextually provided to the
-- editor via 'commandProvider'.
data CopilotCommand
  = Auto
  | Intros
  | Destruct
  | Homomorphism
  | DestructLambdaCase
  | HomomorphismLambdaCase
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Generate a title for the command.
copilotTitle :: CopilotCommand -> T.Text -> T.Text
copilotTitle Auto _ = "Attempt to fill hole"
copilotTitle Intros _ = "Introduce lambda"
copilotTitle Destruct var = "Case split on " <> var
copilotTitle Homomorphism var = "Homomorphic case split on " <> var
copilotTitle DestructLambdaCase _ = "Lambda case split"
copilotTitle HomomorphismLambdaCase _ = "Homomorphic lambda case split"


------------------------------------------------------------------------------
-- | Plugin configuration for tactics
newtype Config = Config
  { cfg_feature_set :: FeatureSet
  }

emptyConfig :: Config
emptyConfig = Config defaultFeatures

instance ToJSON Config where
  toJSON (Config features) = object
    [ "features" .= prettyFeatureSet features
    ]

instance FromJSON Config where
  parseJSON = withObject "Config" $ \obj -> do
    features <- parseFeatureSet <$> obj .: "features"
    pure $ Config features

