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

elim : (P : Interval → Type{ℓ}) → (p0 : P(𝟎)) → (p1 : P(𝟏)) → (Cubical.PathP(\i → P(segment i)) p0 p1) → ((i : Interval) → P(i))
elim(P) p0 _  _  𝟎           = p0
elim(P) _  p1 _  𝟏           = p1
elim(P) _  _  ps (segment i) = ps(i)

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
max = flip ∘₂ (min on₂ flip)

open import Structure.Relator.Properties
open import Type.Cubical.Path.Equality
open import Type.Properties.Singleton

instance
  Interval-unit : IsUnit(Interval)
  IsUnit.unit Interval-unit = 𝟏
  IsUnit.uniqueness Interval-unit {𝟎} = segment
  IsUnit.uniqueness Interval-unit {𝟏} = reflexivity(Cubical.Path)
  IsUnit.uniqueness Interval-unit {segment i} j = segment(Cubical.Interval.max i j)

transp : (P : Interval → Type{ℓ}) → P(𝟎) → P(𝟏)
transp(P) = sub₂(Cubical.Path)(_→ᶠ_) (Cubical.map P(segment))
