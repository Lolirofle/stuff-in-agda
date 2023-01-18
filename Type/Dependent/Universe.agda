module Type.Dependent.Universe where

import Data.Either as Lang
import Lvl
import Numeral.Finite as Lang
import Numeral.Natural as Lang
import Type as Lang
import Type.Dependent.Sigma as Lang
import Type.Identity as Lang
import Type.W as Lang

data Universe : Lang.Type{Lvl.𝟎}
type : Universe → Lang.Type

data Universe where
  𝕟  : Lang.ℕ → Universe
  Id : (a : Universe) → type a → type a → Universe
  Π  : (a : Universe) → (type a → Universe) → Universe
  Σ  : (a : Universe) → (type a → Universe) → Universe
  W  : (a : Universe) → (type a → Universe) → Universe

type(𝕟 n)      = Lang.𝕟(n)
type(Id _ a b) = Lang.Id a b
type(Π a b)    = (A : type a) → type(b(A))
type(Σ a b)    = Lang.Σ (type a) (\A → type(b(A)))
type(W a b)    = Lang.W (type a) (\A → type(b(A)))
