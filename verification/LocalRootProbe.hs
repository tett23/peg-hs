module LocalRootProbe where
newtype Box a = Box a
instance Functor Box where
  fmap f (Box x) = Box (f x)
instance Applicative Box where
  pure = Box
  Box f <*> Box x = Box (f x)
instance Monad Box where
  Box x >>= k = k x
outer :: Integer -> Box Integer
outer x = local x
  where
    local :: Integer -> Box Integer
    local y = do
      a <- pure y
      pure a >> pure a
