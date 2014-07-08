{-# LANGUAGE FlexibleInstances #-}
import Data.Ratio
import Test.QuickSpec
import Test.QuickCheck
import Control.Monad
import Prelude hiding ((/), (\\))
import qualified Prelude

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
type It = Octonion

(\\), (/) :: It -> It -> It
a / b = a * recip b
b \\ a = recip b * a

main = quickSpec [
  withSize 3,
  withDepth 4,
  withTests 50,
  ["a", "b", "c"] `gvars` (it `suchThat` (/= 0) :: Gen It),
  "1" `fun0` (1 :: It),
  "*" `fun2` ((*) :: It -> It -> It),
  "/" `fun2` ((/) :: It -> It -> It),
  "\\" `fun2` ((\\) :: It -> It -> It)]
