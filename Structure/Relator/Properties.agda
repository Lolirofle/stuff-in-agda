module Structure.Relator.Properties where

open import Logic

Reflexivity : {T : Set} → (T → T → Set) → Set
Reflexivity {T} (_▫_) = {x : T} → (x ▫ x)

Symmetry : {T : Set} → (T → T → Set) → Set
Symmetry {T} (_▫_) = {x y : T} → (x ▫ y) → (y ▫ x)

Transitivity : {T : Set} → (T → T → Set) → Set
Transitivity {T} (_▫_) = {x y z : T} → ((x ▫ y) ∧ (y ▫ z)) → (x ▫ z)

Antisymmetry : {T : Set} → (T → T → Set) → (T → T → Set) → Set
Antisymmetry {T} (_▫₁_) (_▫₂_) = {a b : T} → ((a ▫₁ b) ∧ (b ▫₁ a)) → (a ▫₂ b)

Asymmetry : {T : Set} → (T → T → Set) → Set
Asymmetry {T} (_▫_) = {x y : T} → (x ▫ y) → ¬(y ▫ x)

Areflexivity : {T : Set} → (T → T → Set) → Set
Areflexivity {T} (_▫_) = {x : T} → ¬(x ▫ x)
