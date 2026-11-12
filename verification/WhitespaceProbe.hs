import Data.Char (chr, isSpace)

main :: IO ()
main = do
  let scalars = filter (\n -> n < 0xd800 || n > 0xdfff) [0 .. 0x10ffff]
      spaces = filter (isSpace . chr) scalars
  putStrLn ("count=" ++ show (length spaces))
  putStrLn (unwords (map show spaces))
