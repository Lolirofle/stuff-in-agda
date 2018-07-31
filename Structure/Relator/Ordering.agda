module Structure.Relator.Ordering {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
  hiding (antisymmetry ; asymmetry ; transitivity ; reflexivity ; irreflexivity)
open import Type{ℓ₂}

module Weak {T : Type} (_≤_ : T → T → Stmt) where
  record PartialOrder (_≡_ : T → T → Stmt) : Stmt where
    field
     ⦃ antisymmetry ⦄ : Antisymmetry (_≤_) (_≡_)
     ⦃ transitivity ⦄ : Transitivity (_≤_)
     ⦃ reflexivity ⦄  : Reflexivity  (_≤_)

  record TotalOrder (_≡_ : T → T → Stmt) : Stmt where
    field
     ⦃ partialOrder ⦄ : PartialOrder (_≡_)
     ⦃ totality ⦄    : Total (_≤_)

  module Properties where
    record Minimum : Stmt where
      field
        min : T
        minimum : ∀{x : T} → (min ≤ x)
    open Minimum ⦃ ... ⦄ using (min) public

    record Maximum : Stmt where
      field
        max : T
        maximum : ∀{x : T} → (x ≤ max)
    open Maximum ⦃ ... ⦄ using (max) public

    -- LowerBound(P)(x) represents that x is a lower bound of the set {x. P(x)}
    record LowerBound (P : T → Stmt) (l : T) : Stmt where
      field
        lowerBound : ∀{x} → P(x) → (l ≤ x)

    -- UpperBound(P)(x) represents that x is an upper bound of the set {x. P(x)}
    record UpperBound (P : T → Stmt) (u : T) : Stmt where
      field
        upperBound : ∀{x} → P(x) → (x ≤ u)

module Strict {T : Type} (_<_ : T → T → Stmt) where
  record Order : Stmt where
    field
     ⦃ transitivity ⦄  : Transitivity  (_<_)
     ⦃ asymmetry ⦄     : Asymmetry     (_<_)
     ⦃ irreflexivity ⦄ : Irreflexivity (_<_)

  module Properties where
    record Dense : Stmt where
      field
        dense : ∀{x y : T} → (x < y) → ∃(z ↦ (x < z)∧(z < y))

module From-[<][≡] {T : Type} (_<_ : T → T → Stmt) (_≡_ : T → T → Stmt) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = y < x

  -- Lesser than or equals
  _≤_ : T → T → Stmt
  x ≤ y = (x < y) ∨ (x ≡ y)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (x > y) ∨ (x ≡ y)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)

module From-[≤] {T : Type} (_≤_ : T → T → Stmt) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = ¬(x ≤ y)

  -- Lesser than or equals
  _<_ : T → T → Stmt
  x < y = (y > x)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (y ≤ x)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)


module From-[≤][<] {T : Type} (_≤_ : T → T → Stmt) (_<_ : T → T → Stmt) where
  -- Greater than
  _>_ : T → T → Stmt
  x > y = (y < x)

  -- Greater than or equals
  _≥_ : T → T → Stmt
  x ≥ y = (y ≤ x)

  -- In an open interval
  _<_<_ : T → T → T → Stmt
  x < y < z = (x < y) ∧ (y < z)

  -- In an closed interval
  _≤_≤_ : T → T → T → Stmt
  x ≤ y ≤ z = (x ≤ y) ∧ (y ≤ z)

  _≮_ : T → T → Stmt
  x ≮ y = ¬(x < y)

  _≯_ : T → T → Stmt
  x ≯ y = ¬(x > y)

  _≰_ : T → T → Stmt
  x ≰ y = ¬(x ≤ y)

  _≱_ : T → T → Stmt
  x ≱ y = ¬(x ≥ y)
