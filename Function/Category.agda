open import Functional
open import Structure.Operator
open import Structure.Setoid
open import Type

module Function.Category
  {ℓₒ ℓₑ}
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

open import Function.Proofs
open import Logic.Propositional
import      Lvl
open import Structure.Category
open import Structure.Categorical.Properties

private variable ℓ ℓₘ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

-- A category of types and functions.
functionCategory : Category{Obj = Type{ℓₒ}} (_→ᶠ_) ⦃ equiv-func ⦄
Category._∘_            functionCategory = _∘_
Category.id             functionCategory = id
Category.binaryOperator functionCategory = [∘]-func
Category.associativity  functionCategory = Morphism.intro \{a}{b}{c}{d} {f}{g}{h} → [∘]-associativity ⦃ equiv-func ⦄ {f}{g}{h}
Category.identity       functionCategory = [∧]-intro (Morphism.intro ([∘]-identityₗ ⦃ equiv-func ⦄)) (Morphism.intro ([∘]-identityₗ ⦃ equiv-func ⦄))

Functionᶜᵃᵗ : CategoryObject
Functionᶜᵃᵗ = intro functionCategory
