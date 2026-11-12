splitCases :: [Text]
splitCases =
  ["", "A,B", " A , B ", "A(B,C), D", "A[B,C],D", "A,,B", ",A,",
   "A\t,B", "A\xa0,B", "A(x,(y,z)),B", "A),B"]

stringCases :: [(Text, Text)]
stringCases =
  [("expect", "S \"hello\""), ("expect", "S \"\""),
   ("message", "S \"x\""), ("expect", "S \"a\\n\""),
   ("expect", "S \"\\u{41}\""), ("expect", "S \"\\u{}\""),
   ("expect", "S \"\\q\""), ("expect", "S \"unterminated"),
   ("expect", "S \"ok\" extra"), ("expect", "bad-name \"x\""),
   ("expect", "S \"\\u{110000}\""), ("expect", "S \"\\u{d800}\""),
   ("expect", "S \"x\\u{1F600}\""), ("expect", "S \"a\\t\""),
   ("expect", "S\xa0\"x\"")]

main :: IO ()
main = do
  mapM_ (\s -> putStrLn ("split:" ++ T.unpack (T.intercalate "|"
    (map unLoc (splitExports (Loc 0 1 1) s))))) splitCases
  mapM_ showStringArg stringCases
  where
    showStringArg (directive, arg) = case stringArg directive (Loc 0 1 1)
      (Located (Loc 0 1 1) arg) of
      Right (Located _ name, _) -> putStrLn ("string:OK:" ++ T.unpack name)
      Left d -> putStrLn ("string:ERR:" ++ T.unpack (diagMessage d))
