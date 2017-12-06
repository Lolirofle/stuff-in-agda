module Relator.Congruence {ℓ₁} {ℓ₂} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Structure.Function.Domain{ℓ₁}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

infixl 15 _≅_
data _≅_ {X Y : Type} {f : X → Y} (x₁ : X) (x₂ : X) : Stmt where
  instance [≅]-intro : (f(x₁) ≡ f(x₂)) → (x₁ ≅ x₂)

[≅]-elim : ∀{X Y} → ∀{x₁ x₂ : X}{f : X → Y} → (x₁ ≅ x₂) → (f(x₁) ≡ f(x₂))
[≅]-elim ([≅]-intro eq) = eq

instance
  [≅]-reflexivity : ∀{X Y}{f} → Reflexivity {X} (_≅_ {X}{Y}{f})
  reflexivity{{[≅]-reflexivity}} = [≅]-intro [≡]-intro

instance
  [≅]-symmetry : ∀{X Y}{f} → Symmetry {X} (_≅_ {X}{Y}{f})
  symmetry{{[≅]-symmetry}} = ([≅]-intro ∘ symmetry ∘ [≅]-elim)

instance
  [≅]-transitivity : ∀{X Y}{f} → Transitivity {X} (_≅_ {X}{Y}{f})
  transitivity{{[≅]-transitivity}} (eq1) (eq2) = [≅]-intro(([≅]-elim eq1) 🝖 ([≅]-elim eq2))

instance
  [≅]-equivalence : ∀{X Y}{f} → Equivalence {X} (_≅_ {X}{Y}{f})
  [≅]-equivalence = record {
      reflexivity  = [≅]-reflexivity ;
      symmetry     = [≅]-symmetry    ;
      transitivity = [≅]-transitivity
    }

[≅]-to-[≡] : ∀{X Y} → ∀{x₁ x₂ : X}{f : X → Y} → Injective(f) → (x₁ ≅ x₂) → (x₁ ≡ x₂)
[≅]-to-[≡] (injectivity) ([≅]-intro eq) = injectivity(eq)

-- Applies functions to each side of the congruence (TODO: Probably an invalid operation)
-- [≅]-with-[_] : ∀{X₁ X₂ Y} → (F : X₁ → X₂) → ∀{x₁ : X₁}{x₂ : X₁}{f} → (x₁ ≅ x₂) → (F(x₁) ≅ F(x₂))
-- [≅]-with-[_] F {_}{_}{f} = [≅]-intro ∘ ([≡]-with-[_] F) ∘ [≅]-elim

-- ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)
