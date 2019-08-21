module Logic.Predicate {ℓ₁} {ℓ₂} where

open import Functional
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}
open import Type.Empty

------------------------------------------
-- Existential quantification (Existance, Exists)

record ∃ {X : Type} (Pred : X → Stmt) : Stmt where
  instance constructor [∃]-intro
  field
    witness   : X
    ⦃ proof ⦄ : Pred(witness)

[∃]-witness : ∀{X}{Pred} → ∃{X}(Pred) → X
[∃]-witness([∃]-intro(x) ⦃ _ ⦄ ) = x

[∃]-proof : ∀{X}{Pred} → (e : ∃{X}(Pred)) → Pred([∃]-witness(e))
[∃]-proof([∃]-intro(_) ⦃ proof ⦄ ) = proof

[∃]-elim : ∀{X}{Pred}{Z : Stmt} → (∀{x : X} → Pred(x) → Z) → (∃{X} Pred) → Z
[∃]-elim (f) ([∃]-intro(_) ⦃ proof ⦄) = f(proof)

-- syntax ∃ {X} (λ x → f) = ∃[ x ∊ X ] f
-- syntax ∃     (λ x → f) = ∃[ x ] f

------------------------------------------
-- Universal quantification (Forall, All)

∀ₗ : ∀{X : Type} → (Pred : X → Stmt) → Stmt
∀ₗ (Pred) = (∀{x} → Pred(x))

[∀]-intro : ∀{X : Type}{Pred : X → Stmt} → ((a : X) → Pred(a)) → ∀ₗ(x ↦ Pred(x))
[∀]-intro p{a} = p(a)

[∀]-elim : ∀{X : Type}{Pred : X → Stmt} → ∀ₗ(x ↦ Pred(x)) → (a : X) → Pred(a)
[∀]-elim p(a) = p{a}

-- Eliminates universal quantification for a non-empty domain using the witnessed existence which proves that the domain is non-empty.
[∀ₑ]-elim : ∀{X : Type} → ⦃ _ : ◊ X ⦄ → ∀{P : X → Stmt} → ∀ₗ(x ↦ P(x)) → P([◊]-existence)
[∀ₑ]-elim {X} ⦃ proof ⦄ {P} apx = [∀]-elim {X}{P} apx(◊.existence(proof))

syntax ∃{T}(λ x → y) = ∃❪ x ꞉ T ❫․ y
syntax ∀ₗ{T}(λ x → y) = ∀❪ x ꞉ T ❫․ y
