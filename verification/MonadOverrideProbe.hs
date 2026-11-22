{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module MonadOverrideProbe where
import Control.Monad (mapM_)

data Override a = Override Integer a
instance Functor Override where
  fmap f (Override n a) = Override n (f a)
instance Applicative Override where
  pure a = Override 0 a
  Override n f <*> Override m a = Override (n + m + 200) (f a)
instance Monad Override where
  Override n a >>= k = case k a of Override m b -> Override (n + m) b
  Override n _ >> Override m b = Override (n + m + 10) b
  return a = Override 100 a

overrideStep :: Integer -> Integer -> Integer
overrideStep a b = case do Override a (); Override b (7 :: Integer) of Override n _ -> n
overrideDo :: Integer
overrideDo = overrideStep 1 2
overrideOperatorStep :: Integer -> Integer -> Integer
overrideOperatorStep a b = case Override a () >> Override b (7 :: Integer) of Override n _ -> n
overrideOperator :: Integer
overrideOperator = overrideOperatorStep 1 2
overridden_ :: Integer
overridden_ = case mapM_ (\n -> Override n ()) [1,2,3] of Override n _ -> n
