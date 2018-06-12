module Relator.Congruence.Proofs {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Structure.Function.Domain{ℓ₁}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Relator.Congruence{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

instance
  [≅]-reflexivity : ∀{X Y}{f : X → Y} → Reflexivity {X} (_≅_of f)
  reflexivity ⦃ [≅]-reflexivity ⦄ = [≅]-intro [≡]-intro

instance
  [≅]-symmetry : ∀{X Y}{f : X → Y} → Symmetry {X} (_≅_of f)
  symmetry ⦃ [≅]-symmetry ⦄ = ([≅]-intro ∘ symmetry ∘ [≅]-elim)

instance
  [≅]-transitivity : ∀{X Y}{f : X → Y} → Transitivity {X} (_≅_of f)
  transitivity ⦃ [≅]-transitivity ⦄ (eq1) (eq2) = [≅]-intro(([≅]-elim eq1) 🝖 ([≅]-elim eq2))

instance
  [≅]-equivalence : ∀{X Y}{f : X → Y} → Equivalence {X} (_≅_of f)
  [≅]-equivalence = record {
      reflexivity  = [≅]-reflexivity ;
      symmetry     = [≅]-symmetry    ;
      transitivity = [≅]-transitivity
    }

[≅]-to-[≡] : ∀{X Y}{f : X → Y} → Injective(f) ↔ (∀{x₁ x₂ : X} → (x₁ ≅ x₂ of f) → (x₁ ≡ x₂))
[≅]-to-[≡] {X}{Y}{f} = [↔]-intro (_∘ [≅]-intro) (_∘ [≅]-elim) where

[≅]-composition : ∀{X₁ X₂ Y} → ∀{x₁ x₂ : X₁}{g : X₁ → X₂} → (x₁ ≅ x₂ of g) → ∀{f : X₂ → Y} → (g(x₁) ≅ g(x₂) of f)
[≅]-composition ([≅]-intro (fx₁≡fx₂)) {f} = [≅]-intro ([≡]-with(f) (fx₁≡fx₂))
  -- x₁ ≅ x₂
  -- ⇔ g(x₁) = g(x₂)
  -- ⇒ f(g(x₁)) = f(g(x₂))
