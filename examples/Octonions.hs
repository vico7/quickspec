{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables #-}
import Data.Ratio
import Test.QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude
import Data.Typeable

class Fractional a => Conj a where
  conj :: a -> a
  norm :: a -> Rational
  it :: Gen a

instance Conj Rational where
  conj x = x
  norm x = x*x
  it = liftM2 (Prelude./) (elements [-10..10]) (elements [1..10])

instance Conj a => Conj (a, a) where
  conj (x, y) = (conj x, negate y)
  norm (x, y) = norm x + norm y
  it = liftM2 (,) it it

instance Conj a => Num (a, a) where
  fromInteger n = (fromInteger n, 0)
  (x, y) + (z, w) = (x + z, y + w)
  (a, b) * (c, d) = (a * c - conj d * b, d * a + b * conj c)
  negate (x, y) = (negate x, negate y)

instance Conj a => Fractional (a, a) where
  fromRational x = (fromRational x, 0)
  recip x = conj x * fromRational (recip (norm x))

type Complex = (Rational, Rational)
type Quaternion = (Complex, Complex)
type Octonion = (Quaternion, Quaternion)
newtype It = It Octonion deriving (Eq, Ord, Num, Typeable, Fractional)
newtype Fun = Fun (It -> It) deriving (Arbitrary, CoArbitrary, Typeable)

instance Arbitrary It where arbitrary = fmap It it
instance CoArbitrary It where coarbitrary (It x) = coarbitrary x

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

l, r, l1, r1 :: It -> Fun
l x = Fun (\y -> x * y)
r x = Fun (\y -> y * x)
l1 x = Fun (\y -> x \\ y)
r1 x = Fun (\y -> y / x)

sig1 = [
  withSize 3,
  withDepth 4,
  withTests 10,
  ["a", "b", "c"] `vars` (undefined :: It),
  "1" `fun0` (1 :: It),
  "*" `fun2` ((*) :: It -> It -> It),
  "/" `fun2` ((/) :: It -> It -> It),
  "\\" `fun2` ((\\) :: It -> It -> It)]

sig2 = [
  withSize 3,
  withDepth 4,
  withTests 10,
  ["f", "g", "h"] `vars` (undefined :: Fun),
  ["a", "b", "c"] `vars` (undefined :: It),
  observer2 (\x (Fun f :: Fun) -> f x),
  "*" `fun2` ((*) :: It -> It -> It),
  "1" `fun0` (1 :: It),
  "1" `blind0` (Fun (\x -> x)),
  "." `blind2` (\(Fun f) (Fun g) -> Fun (\x -> f (g x))),
  "l" `blind1` l,
  "r" `blind1` r,
  "l1" `blind1` l1,
  "r1" `blind1` r1]

main = quickSpec sig1
