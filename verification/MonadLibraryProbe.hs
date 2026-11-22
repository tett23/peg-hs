{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module MonadLibraryProbe where
import Control.Monad (mapM, mapM_)
import qualified GHC.Base as Base (mapM)
import Data.Maybe (mapMaybe)

-- The operations deliberately differ: translation must follow the actual
-- methods and defaults, without adding the Monad laws as a premise.
data Mark a = Mark Integer a
instance Functor Mark where
  fmap f (Mark n a) = Mark n (f a)
instance Applicative Mark where
  pure a = Mark 0 a
  Mark n f <*> Mark m a = Mark (n + m + 100) (f a)
instance Monad Mark where
  Mark n a >>= k = case k a of Mark m b -> Mark (n + m) b
  return a = Mark 999 a

defaultStep :: Integer -> Integer -> Integer
defaultStep a b = case do Mark a (); Mark b (7 :: Integer) of Mark n _ -> n
defaultDo :: Integer
defaultDo = defaultStep 1 2
defaultOperatorStep :: Integer -> Integer -> Integer
defaultOperatorStep a b = case Mark a () >> Mark b (7 :: Integer) of Mark n _ -> n
defaultOperator :: Integer
defaultOperator = defaultOperatorStep 1 2
mapped :: Integer
mapped = case mapM (\n -> Mark n (n + 1)) [1,2,3] of Mark n values -> n + sum values
mappedBase :: Integer
mappedBase = case Base.mapM (\n -> Mark n (n + 1)) [1,2,3] of Mark n values -> n + sum values
mapped_ :: Integer
mapped_ = case mapM_ (\n -> Mark n ()) [1,2,3] of Mark n _ -> n
emptyMapped_ :: Integer
emptyMapped_ = case mapM_ (\n -> Mark n ()) ([] :: [Integer]) of Mark n _ -> n
filtered :: Integer
filtered = sum (mapMaybe (\n -> if n > 0 then Just n else Nothing) [-1,0,1,2])
