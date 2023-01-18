module Structure.IEEE754 where

open import Data.Boolean
import      Lvl
open import Type

private variable ℓ : Lvl.Level

open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Sign
postulate 𝕫 : ℕ → ℕ → Type{Lvl.𝟎}

record FloatingPointRepresentation(Float : Type{ℓ}) : Type{ℓ} where
  field
    radix         : ℕ
    precision     : ℕ
    exponentRange : ℕ

  field
    sign        : Float → Sign
    exponent    : Float → 𝕫 (𝐒(exponentRange)) exponentRange
    significand : Float → (𝕟(precision) → 𝕟(radix))


record FloatingPoint(Float : Type{ℓ}) : Type{ℓ} where
  field
    nextUp   : Float → Float
    nextDown : Float → Float
    rem      : Float → Float → Float

    _≡?_ : Float → Float → Bool
    _≢?_ : Float → Float → Bool
    _≤?_ : Float → Float → Bool
    _≰?_ : Float → Float → Bool
    _<?_ : Float → Float → Bool
    _≮?_ : Float → Float → Bool
    _≥?_ : Float → Float → Bool
    _≱?_ : Float → Float → Bool
    _>?_ : Float → Float → Bool
    _≯?_ : Float → Float → Bool

    isNormal       : Float → Bool
    isSubnormal    : Float → Bool
    isFinite       : Float → Bool
    isInfinite     : Float → Bool
    isNaN          : Float → Bool
    isNegativeZero : Float → Bool
    isSafeInteger  : Float → Bool

    _+_   : Float → Float → Float
    _−_   : Float → Float → Float
    _⋅_   : Float → Float → Float
    _/_   : Float → Float → Float
    sqrt  : Float → Float

    −_    : Float → Float
    abs   : Float → Float


    _^_   : Float → Float → Float
    root  : Float → Float → Float
    log   : Float → Float → Float
    exp   : Float → Float
    ln    : Float → Float
    sin   : Float → Float
    cos   : Float → Float
    tan   : Float → Float
    asin  : Float → Float
    acos  : Float → Float
    atan  : Float → Float
    sinh  : Float → Float
    cosh  : Float → Float
    tanh  : Float → Float
    asinh : Float → Float
    acosh : Float → Float
    atanh : Float → Float
    atan2 : Float → Float → Float
    hypot : Float → Float → Float
