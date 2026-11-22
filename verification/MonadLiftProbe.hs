module MonadLiftProbe where
import Control.Monad (mapM)

data Lift a = Lift Integer a
instance Functor Lift where
  fmap f (Lift n a) = Lift n (f a)
instance Applicative Lift where
  pure a = Lift 0 a
  Lift n f <*> Lift m a = Lift (n + m + 100) (f a)
  liftA2 f (Lift n a) (Lift m b) = Lift (n + m + 50) (f a b)
instance Monad Lift where
  Lift n a >>= k = case k a of Lift m b -> Lift (n + m) b

mappedLift :: Integer
mappedLift = case mapM (\n -> Lift n (n + 1)) [1,2,3] of Lift n values -> n + sum values
