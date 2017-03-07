module Data where

open import Type

data Either (T₁ : Type) (T₂ : Type) : Type where
  left : T₁ → Either T₁ T₂
  right : T₂ → Either T₁ T₂

swap : ∀ {T₁ T₂} → Either T₁ T₂ → Either T₂ T₁
swap (left t) = right t
swap (right t) = left t



Option : Type → Type
Option T = Either Unit T

some : ∀ {T} → T → Option T
some = right

none : ∀ {T} → Option T
none = left unit

map : ∀ {T₁ T₂} → (T₁ → T₂) → (Option T₁) → (Option T₂)
map f (right x) = some(f(x))
map f (left unit) = none
