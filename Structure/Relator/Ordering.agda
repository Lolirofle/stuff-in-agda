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
    instance constructor intro
    field
     ⦃ antisymmetry ⦄ : Antisymmetry (_≤_) (_≡_)
     ⦃ transitivity ⦄ : Transitivity (_≤_)
     ⦃ reflexivity ⦄  : Reflexivity  (_≤_)

  record TotalOrder (_≡_ : T → T → Stmt) : Stmt where
    instance constructor intro
    field
     ⦃ partialOrder ⦄ : PartialOrder (_≡_)
     ⦃ totality ⦄     : SymmetricallyTotal (_≤_)

  module Properties where
    record Minimum (min : T) : Stmt where
      constructor intro
      field
        proof : ∀{x : T} → (min ≤ x)

    record Maximum (max : T) : Stmt where
      constructor intro
      field
        proof : ∀{x : T} → (x ≤ max)

  min : ⦃ _ : ∃(Properties.Minimum) ⦄ → T
  min ⦃ e ⦄ = [∃]-witness e

  max : ⦃ _ : ∃(Properties.Maximum) ⦄ → T
  max ⦃ e ⦄ = [∃]-witness e

module Strict {T : Type} (_<_ : T → T → Stmt) where
  record Order : Stmt where
    instance constructor intro
    field
     ⦃ transitivity ⦄  : Transitivity  (_<_)
     ⦃ asymmetry ⦄     : Asymmetry     (_<_)
     ⦃ irreflexivity ⦄ : Irreflexivity (_<_)

  module Properties where
    record Dense : Stmt where
      field
        between : T → T → T
        left    : ∀{x y : T} → (x < y) → (x < between(x)(y))
        right   : ∀{x y : T} → (x < y) → (between(x)(y) < y)

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
  x ≯ y = (x ≤ y)

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
