module Structure.Relator.Ordering where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Logic.Propositional.Theorems
open import Structure.Relator.Properties
  hiding (antisymmetry ; asymmetry ; transitivity ; reflexivity ; irreflexivity)
open import Type
open import Type.Empty

module Weak {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  record PartialOrder {ℓ₃} (_≡_ : T → T → Stmt{ℓ₃}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    instance constructor intro
    field
     ⦃ antisymmetry ⦄ : Antisymmetry (_≤_) (_≡_)
     ⦃ transitivity ⦄ : Transitivity (_≤_)
     ⦃ reflexivity ⦄  : Reflexivity  (_≤_)

  record TotalOrder {ℓ₃} (_≡_ : T → T → Stmt{ℓ₃}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    instance constructor intro
    field
     ⦃ partialOrder ⦄ : PartialOrder (_≡_)
     ⦃ totality ⦄     : ConverseTotal (_≤_)

  module Properties where
    record Minimum (min : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        proof : ∀{x : T} → (min ≤ x)

    record Maximum (max : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        proof : ∀{x : T} → (x ≤ max)

    module _ {ℓ₃} where
      record LowerBoundOf (P : T → Stmt{ℓ₃}) (b : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
        constructor intro
        field
          proof : ∀{x : T} → P(x) → (b ≤ x)

      record UpperBoundOf (P : T → Stmt{ℓ₃}) (b : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
        constructor intro
        field
          proof : ∀{x : T} → P(x) → (x ≤ b)

    module _ {ℓ₃} where
      record SupremumOf (P : T → Stmt{ℓ₃}) (sup : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
        constructor intro
        field
          bound : UpperBoundOf(P) (sup)
          extreme : LowerBoundOf(UpperBoundOf(P)) (sup)

      record InfimumOf (P : T → Stmt{ℓ₃}) (inf : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
        constructor intro
        field
          bound : LowerBoundOf(P) (inf)
          extreme : UpperBoundOf(LowerBoundOf(P)) (inf)

  min : ⦃ _ : ∃(Properties.Minimum) ⦄ → T
  min ⦃ e ⦄ = [∃]-witness e

  max : ⦃ _ : ∃(Properties.Maximum) ⦄ → T
  max ⦃ e ⦄ = [∃]-witness e

  module _ {ℓ₃} where
    sup : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Properties.SupremumOf(P)) ⦄ → T
    sup _ ⦃ e ⦄ = [∃]-witness e

    inf : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Properties.InfimumOf(P)) ⦄ → T
    inf _ ⦃ e ⦄ = [∃]-witness e

module Strict {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) where
  record Order : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    instance constructor intro
    field
     ⦃ transitivity ⦄  : Transitivity  (_<_)
     ⦃ asymmetry ⦄     : Asymmetry     (_<_)
     ⦃ irreflexivity ⦄ : Irreflexivity (_<_)

  module Properties where
    record Dense : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      field
        between : T → T → T
        left    : ∀{x y : T} → (x < y) → (x < between(x)(y))
        right   : ∀{x y : T} → (x < y) → (between(x)(y) < y)
