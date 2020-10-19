{-# LANGUAGE TypeApplications #-}

module Machinery where

import           Control.Arrow
import           Data.Maybe
import qualified GHC as G
import           GhcMonad
import           HIE.Bios
import           HIE.Bios.Environment
import           HIE.Bios.Ghc.Api


typecheck :: FilePath -> IO G.TypecheckedModule
typecheck
  = fmap (fromJust . fst)
  . runGhc
  . loadFile
  . (id &&& id)
  . mappend "test/testdata/"


runGhc :: Ghc a -> IO a
runGhc m = do
  cradle <- loadCradle "test/testdata/hie.yaml"
  mb <- getRuntimeGhcLibDir cradle
  CradleSuccess mlibdir <- pure mb
  G.runGhc (Just mlibdir) $ do
    _ <- initializeFlagsWithCradle mlibdir cradle
    m

