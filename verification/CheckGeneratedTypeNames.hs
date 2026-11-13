module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.Text as T
import GHC (getSessionDynFlags, runGhc)
import GHC.Data.FastString (mkFastString, unpackFS)
import GHC.Data.StringBuffer (stringToStringBuffer)
import GHC.Driver.Config.Parser (initParserOpts)
import GHC.Parser.Lexer (ParseResult (..), Token (..), lexTokenStream)
import GHC.Types.SrcLoc (mkRealSrcLoc, unLoc)
import Peg.Grammar.Types (generatedTypeName)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
  [libdir] <- getArgs
  options <- runGhc (Just libdir) (initParserOpts <$> getSessionDynFlags)
  let loc = mkRealSrcLoc (mkFastString "GeneratedTypeName") 1 1
  forM_ ["expr", "_rule", "数式", "ǅigit", "a'1", "do", "mdo"] $ \rule ->
    forM_ [" ", ")", "]", "\n"] $ \separator -> do
      let name = T.unpack (generatedTypeName (T.pack rule))
          source = "(" ++ name ++ separator ++ " Next"
          endsCorrectly tokens = case (separator, tokens) of
            (")", ITcparen : rest) -> next rest
            ("]", ITcbrack : rest) -> next rest
            (" ", rest) -> next rest
            ("\n", rest) -> next rest
            _ -> False
          next (ITconid ident : _) = unpackFS ident == "Next"
          next _ = False
      case lexTokenStream options (stringToStringBuffer source) loc of
        POk _ located | IToparen : ITconid ident : rest <- map unLoc located ->
          unless (unpackFS ident == name && endsCorrectly rest) (die (show source))
        _ -> die ("unexpected tokens for " ++ show source)
