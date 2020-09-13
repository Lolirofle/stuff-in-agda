module Functional.Combinations where

open import Type

-- TODO: Generalize these. Probably by lists and foldᵣ of combination and rotation construction functions. Also categorically or dependently
rotate₃Fn₃Op₂ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → A → A → B) → (B → B → B) → (A → A → A → B)
rotate₃Fn₃Op₂(F)(_▫_) a b c = (F a b c) ▫ ((F b c a) ▫ (F c a b))

combine₃Fn₂Op₂ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → A → B) → (B → B → B) → (A → A → A → B)
combine₃Fn₂Op₂(F)(_▫_) a b c = (F a b) ▫ ((F a c) ▫ (F b c))

all₃Fn₁Op₂ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → (B → B → B) → (A → A → A → B)
all₃Fn₁Op₂(F)(_▫_) a b c = (F a) ▫ ((F b) ▫ (F c))

combine₄Fn₃Op₂ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → A → A → B) → (B → B → B) → (A → A → A → A → B)
combine₄Fn₃Op₂(F)(_▫_) a b c d = (F a b c) ▫ ((F a b d) ▫ ((F a c d) ▫ (F b c d)))
