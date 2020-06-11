{-# OPTIONS --cubical #-}

module Type.Cubical.InductiveInterval where

open import Functional
import      Lvl
open import Type
import      Type.Cubical             as Cubical
import      Type.Cubical.Path        as Cubical
import      Type.Cubical.Path.Proofs as Cubical

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B P : Type{ℓ}

data Interval : Type{Lvl.𝟎} where
  𝟎 : Interval
  𝟏 : Interval
  segment : Cubical.Path 𝟎 𝟏

flip : Interval → Interval
flip 𝟎 = 𝟏
flip 𝟏 = 𝟎
flip (segment i) = segment(Cubical.Interval.flip i)

min : Interval → Interval → Interval
min 𝟎 𝟎 = 𝟎
min 𝟎 𝟏 = 𝟎
min 𝟏 𝟎 = 𝟎
min 𝟏 𝟏 = 𝟏
min 𝟎           (segment i) = 𝟎
min 𝟏           (segment i) = segment i
min (segment i) 𝟎           = 𝟎
min (segment i) 𝟏           = segment i
min (segment i) (segment j) = segment(Cubical.Interval.min i j)

max : Interval → Interval → Interval
max 𝟎 𝟎 = 𝟎
max 𝟎 𝟏 = 𝟏
max 𝟏 𝟎 = 𝟏
max 𝟏 𝟏 = 𝟏
max 𝟎           (segment i) = segment i
max 𝟏           (segment i) = 𝟏
max (segment i) 𝟎           = segment i
max (segment i) 𝟏           = 𝟏
max (segment i) (segment j) = segment(Cubical.Interval.max i j)

-- TODO: What?
-- transp : (f : Interval → Type{ℓ}) → f(𝟎) → f(𝟏)
-- transp f a0 = Cubical.Path-to-[→] (Cubical.map-path f segment) a0
