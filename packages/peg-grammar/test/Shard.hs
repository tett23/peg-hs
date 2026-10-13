{-# LANGUAGE LambdaCase #-}

-- | Running a part of the tests, so that CI runs the suite in several jobs,
-- and properties split into parts, so that no single test is too long to
-- share out (ADR 0042).
module Shard
  ( Shard (..)
  , sharded
  , shardTree
  , leafNames
  , chunkedProperty
  , chunks
  , shardTests
  ) where

import Data.List (sort)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Options
import Test.Tasty.QuickCheck
import Test.Tasty.Runners (TestTree (..))
import Text.Read (readMaybe)

-- | @--shard i/n@: run the leaves whose position, counted in the order of
-- the tree, leaves the remainder @i - 1@ when divided by @n@.
newtype Shard = Shard (Maybe (Int, Int))
  deriving (Eq, Show)

instance IsOption Shard where
  defaultValue = Shard Nothing
  parseValue s = case break (== '/') s of
    (a, '/' : b)
      | Just i <- readMaybe a
      , Just n <- readMaybe b
      , 1 <= i
      , i <= n ->
          Just (Shard (Just (i, n)))
    _ -> Nothing
  optionName = pure "shard"
  optionHelp = pure "Run only the I-th of N parts of the tests, as I/N (ADR 0042)"

-- | The tree, or the part of it that the option @--shard@ selects.
sharded :: TestTree -> TestTree
sharded t = AskOptions $ \opts -> case lookupOption opts of
  Shard Nothing -> t
  Shard (Just (i, n)) -> shardTree opts i n t

-- | The leaves of part @i@ of @n@, keeping the groups that still have
-- leaves. A resource and its tests count as one leaf.
shardTree :: OptionSet -> Int -> Int -> TestTree -> TestTree
shardTree opts0 i n t = maybe (TestGroup "" []) id (fst (go opts0 t 0))
  where
    keep k = k `mod` n == i - 1
    go :: OptionSet -> TestTree -> Int -> (Maybe TestTree, Int)
    go opts tree k = case tree of
      SingleTest name x -> (if keep k then Just (SingleTest name x) else Nothing, k + 1)
      TestGroup name ts ->
        let (ts', k') = goList opts ts k
         in (if null ts' then Nothing else Just (TestGroup name ts'), k')
      PlusTestOptions f t' -> let (r, k') = go (f opts) t' k in (PlusTestOptions f <$> r, k')
      AskOptions f -> go opts (f opts) k
      WithResource spec f -> (if keep k then Just (WithResource spec f) else Nothing, k + 1)
      After d e t' -> let (r, k') = go opts t' k in (After d e <$> r, k')
    goList _ [] k = ([], k)
    goList opts (x : xs) k =
      let (r, k') = go opts x k
          (rs, k'') = goList opts xs k'
       in (maybe rs (: rs) r, k'')

-- | The paths of the leaves, in the order of the tree.
leafNames :: OptionSet -> TestTree -> [[String]]
leafNames = go []
  where
    go path opts = \case
      SingleTest name _ -> [reverse (name : path)]
      TestGroup name ts -> concatMap (go (name : path) opts) ts
      PlusTestOptions f t -> go path (f opts) t
      AskOptions f -> go path opts (f opts)
      WithResource _ _ -> [reverse ("<resource>" : path)]
      After _ _ t -> go path opts t

-- | The number of parts of a split property.
chunks :: Int
chunks = 4

-- | A property of @cases@ cases as 'chunks' tests next to each other, each
-- of a part of the cases. The property gets the number of its part, to make
-- its generators different with 'variant': with @--quickcheck-replay@,
-- every test gets the same seed.
chunkedProperty :: TestName -> Int -> (Int -> Property) -> [TestTree]
chunkedProperty name cases p =
  [ testProperty (name <> " (" <> show i <> "/" <> show chunks <> ")") (withNumTests (cases `div` chunks) (p i))
  | i <- [1 .. chunks]
  ]

-- Tests ------------------------------------------------------------------------

shardTests :: TestTree
shardTests =
  testGroup
    "sharding the tests (ADR 0042)"
    [ testProperty "the parts make up the leaves, without overlap, and differ by at most one leaf" $
        forAllBlind genTree $ \t -> forAll (choose (1, 5)) $ \n ->
          let parts = [leafNames mempty (shardTree mempty i n t) | i <- [1 .. n]]
              sizes = map length parts
           in sort (concat parts) === sort (leafNames mempty t)
                .&&. (maximum sizes - minimum sizes <= 1)
    , testProperty "no group without leaves is kept" $
        forAllBlind genTree $ \t -> forAll (choose (1, 5)) $ \n ->
          conjoin [counterexample (show i) (noEmptyGroup (shardTree mempty i n t)) | i <- [1 .. n]]
    , testCase "the option" $
        map (parseValue :: String -> Maybe Shard) ["1/3", "3/3", "0/3", "4/3", "x", "3", "1/0"]
          @?= [Just (Shard (Just (1, 3))), Just (Shard (Just (3, 3))), Nothing, Nothing, Nothing, Nothing, Nothing]
    , testCase "the option goes through the tree to the leaves" $ do
        let t = sharded (testGroup "g" [testCase (show k) (pure ()) | k <- [0 .. 5 :: Int]])
            opts = setOption (Shard (Just (2, 3))) mempty
        leafNames opts t @?= [["g", "1"], ["g", "4"]]
    ]
  where
    noEmptyGroup = \case
      TestGroup "" [] -> True
      t -> go t
      where
        go = \case
          TestGroup _ ts -> not (null ts) && all go ts
          PlusTestOptions _ t -> go t
          _ -> True

-- Trees of groups and leaves with distinct names.
genTree :: Gen TestTree
genTree = fst <$> sized (\s -> tree (min 3 (s `div` 20 + 1)) 0)
  where
    tree :: Int -> Int -> Gen (TestTree, Int)
    tree depth k = do
      m <- choose (0, 4 :: Int)
      (ts, k') <- children depth m k
      pure (testGroup ("group" <> show k) ts, k' + 1)
    children _ 0 k = pure ([], k)
    children depth m k = do
      leaf <- if depth <= 0 then pure True else frequency [(3, pure True), (1, pure False)]
      (t, k') <-
        if leaf
          then pure (testCase ("leaf" <> show k) (pure ()), k + 1)
          else tree (depth - 1) (k + 1)
      (ts, k'') <- children depth (m - 1) k'
      pure (t : ts, k'')

