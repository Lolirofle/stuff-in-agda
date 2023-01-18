module Type.W.Proofs where

open import Logic.Propositional
import      Lvl
open import Type
open import Type.Dependent.Sigma
open import Type.W

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

-- A W-type is empty when every constructor is recursive (when no constructor is a base case).
W-emptyᵣ : ((a : A) → B(a)) → ¬(W A B)
W-emptyᵣ ab (sup a w) = W-emptyᵣ ab (w(ab a))

-- A W-type is inhabited when there is a non-recursive constructor (when there is a base case).
W-inhabitedᵣ : Σ A (\a → ¬ B(a)) → (W A B)
W-inhabitedᵣ (intro a anb) = sup a \b → [⊥]-elim (anb b)

module _ (nnb : ∀{a : A} → ¬¬(B(a)) → B(a)) where
  W-emptyₗ : ¬(W A B) → ((a : A) → B(a))
  W-emptyₗ nw a = nnb \nb → nw (sup a \b → [⊥]-elim (nb b))

module _ (em-b : ∀{a : A} → B(a) ∨ (¬ B(a))) where
  W-inhabitedₗ : (W A B) → Σ A (\a → ¬ B(a))
  W-inhabitedₗ (sup a w) = [∨]-elim (\b → W-inhabitedₗ (w b)) (\nb → intro a nb) em-b
