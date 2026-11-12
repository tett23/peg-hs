numbers :: [Integer]
numbers = [0, 1, 9, 10, 99, 100, 9223372036854775807, 9223372036854775808, 10^100]

cases :: [([Text], [Text], Integer)]
cases =
  [([], [], 0), (["T'0"], [], 0), (["T'0"], ["T'1"], 0),
   (["T'0", "T'1", "T'2"], [], 0), (["T'0"], ["T'5"], 5),
   (["Other'0", "T'0"], ["T'2", "T'1"], 0)]

main :: IO ()
main = do
  mapM_ (TIO.putStrLn . probe [] [] ) numbers
  mapM_ (\(original, generated, start) ->
    TIO.putStrLn (probe original generated start)) cases
