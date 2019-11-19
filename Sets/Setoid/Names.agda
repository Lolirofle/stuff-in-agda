module Sets.Setoid.Names where

open import Data.Tuple
open import Functional
open import Functional.Equals
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}

-- TODO: Probably incorrect
-- Choice : let _ = A , B in ⦃ equiv-B : Equiv(B) ⦄ → (A → B → Stmt{ℓ}) → Stmt
-- Choice {A = A} {B = B} (_▫_) = (∀{x} → ∃(y ↦ x ▫ y)) → ∃{Obj = A → B}(f ↦ (∀{x} → (x ▫ f(x))) ∧ (∀{x y} → (x ▫ y) → (f(x) ≡ y)))

-- Choice-[∘]-inverseᵣ : let _ = A in ⦃ equiv-B : Equiv(B) ⦄ → (A → B → Stmt{ℓ}) → Stmt
-- Choice-[∘]-inverseᵣ {A = A} {B = B} (f) = ∃{Obj = B → A}(f⁻¹ ↦ f ∘ f⁻¹ ⊜ id)
