{-# OPTIONS --cubical #-}

module Type.Cubical.InductivePath where

open import Functional
import      Lvl
open import Type
import      Type.Cubical as Cubical
open import Type.Cubical.InductiveInterval

private variable ℓ : Lvl.Level
private variable A B P : Type{ℓ}
private variable x y : A

data Path {P : Type{ℓ}} : P → P → Type{ℓ} where
  intro : (p : Interval → P) → Path(p(𝟎)) (p(𝟏))

point : (x : P) → Path x x
point x = intro(const x)

reverse : Path x y → Path y x
reverse (intro f) = intro(f ∘ flip)
