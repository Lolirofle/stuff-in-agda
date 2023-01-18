open import Structure.Category
open import Structure.Category.Monoidal

-- Enriched categories.
-- A generalization of the usual set definition of categories (this type of generalization is called enrichment).
-- `Morphism` (hom-set) is an object in C.
-- Operators (_∘_) and elements (id) in the structure are morphisms in C.
-- These are called categories enriched over C.
-- Also called: Enriched category, internal category, category object.
module Structure.Category.Enriched.Category
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ})
  ⦃ M : Monoidalᶜᵃᵗ(C) ⦄
  where

open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Type

open CategoryObject(C) renaming (Object to Objectₘ ; Morphism to Morphismₘ ; _∘_ to _∘ₘ_ ; id to idₘ)
open ArrowNotation renaming (_⟶_ to _⟶ₘ_)
open Monoidalᶜᵃᵗ(M) renaming (unitObject to 𝟏)

private variable ℓ : Lvl.Level

record Signature₀ : Type{ℓₒ Lvl.⊔ Lvl.𝐒(ℓ)} where
  constructor _,_
  field
    Object : Type{ℓ}
    Morphism : Object → Object → Objectₘ
  _⟶_ = Morphism

record Signature₁(s₀ : Signature₀{ℓ}) : Type{ℓₘ Lvl.⊔ ℓ} where
  constructor _,_
  open Signature₀(s₀)
  field
    ∘  : ∀(x)(y)(z) → (((y ⟶ z) ⊗ (x ⟶ y)) ⟶ₘ (x ⟶ z))
    id : ∀(x) → (𝟏 ⟶ₘ (x ⟶ x))

record Conditions {s₀ : Signature₀{ℓ}} (s₁ : Signature₁(s₀)) : Type{ℓₑ Lvl.⊔ ℓ} where
  constructor intro
  open Signature₀(s₀)
  open Signature₁(s₁)
  field
    associativity-condition : ∀{a b c d} → ((∘ a c d) ∘ₘ (idₘ <⊗> (∘ a b c)) ∘ₘ α(c ⟶ d)(b ⟶ c)(a ⟶ b) ≡ (∘ a b d) ∘ₘ ((∘ b c d) <⊗> idₘ))
    unitalityₗ-condition : ∀{a b} → ((∘ a b b) ∘ₘ (id(b) <⊗> idₘ) ≡ υₗ(a ⟶ b))
    unitalityᵣ-condition : ∀{a b} → ((∘ a a b) ∘ₘ (idₘ <⊗> id(a)) ≡ υᵣ(a ⟶ b))
