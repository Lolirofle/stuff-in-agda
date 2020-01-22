module Relator.Congruence.Proofs where

import      Lvl
open import Functional
open import Function.Names
open import Logic.Propositional
open import Logic.Predicate
-- TODO: open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Relator.Congruence
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}}{Y : Type{ℓ₂}} {f : X → Y} where
  instance
    [≅]-reflexivity : Reflexivity (_≅_of f)
    Reflexivity.proof([≅]-reflexivity) = [≅]-intro [≡]-intro

  instance
    [≅]-symmetry : Symmetry (_≅_of f)
    Symmetry.proof([≅]-symmetry) = ([≅]-intro ∘ symmetry(_≡_) ∘ [≅]-elim)

  instance
    [≅]-transitivity : Transitivity (_≅_of f)
    Transitivity.proof([≅]-transitivity) (eq1) (eq2) = [≅]-intro(([≅]-elim eq1) 🝖 ([≅]-elim eq2))

  instance
    [≅]-equivalence : Equivalence (_≅_of f)
    [≅]-equivalence = record {
        reflexivity  = [≅]-reflexivity ;
        symmetry     = [≅]-symmetry    ;
        transitivity = [≅]-transitivity
      }

  [≅]-to-[≡] : Injective(f) ↔ (∀{x₁ x₂ : X} → (x₁ ≅ x₂ of f) → (x₁ ≡ x₂))
  [≅]-to-[≡] = [↔]-intro (_∘ [≅]-intro) (_∘ [≅]-elim) where

module _ {ℓ₁ ℓ₂ ℓ₃} {X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{Y : Type{ℓ₃}} where
  [≅]-composition : ∀{x₁ x₂ : X₁}{g : X₁ → X₂} → (x₁ ≅ x₂ of g) → ∀{f : X₂ → Y} → (g(x₁) ≅ g(x₂) of f)
  [≅]-composition ([≅]-intro (fx₁≡fx₂)) {f} = [≅]-intro ([≡]-with(f) (fx₁≡fx₂))
    -- x₁ ≅ x₂
    -- ⇔ g(x₁) = g(x₂)
    -- ⇒ f(g(x₁)) = f(g(x₂))
