-- | The versions of GHC that @peg-hs parse@ compiles the parser with: those
-- whose base the packages of peg-hs support (ADR 0045).
module GhcVersion (supportedGhc, supportedGhcText) where

import Data.List (isPrefixOf)

supportedSeries :: [String]
supportedSeries = ["9.10", "9.12", "9.14"]

-- | Whether the output of @ghc --numeric-version@ is a supported version.
supportedGhc :: String -> Bool
supportedGhc v = any (\s -> (s <> ".") `isPrefixOf` v) supportedSeries

-- | The supported versions, for messages.
supportedGhcText :: String
supportedGhcText = "GHC 9.10, 9.12 or 9.14"
