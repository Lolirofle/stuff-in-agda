module Logic.Predicate {ℓ₁} {ℓ₂} where

open import Functional
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}

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

------------------------------------------
-- Universal quantification with non-empty domain
-- This makes the following true: (∀ₑx. P(x)) → (∃x. P(x))

record ∀ₑ {X : Type} (Pred : X → Stmt) : Stmt where
  constructor [∀ₑ]-intro
  field
    element        : X
    quantification : ∀ₗ Pred

[∀ₑ]-elim : ∀{X : Type}{Pred : X → Stmt} → ∀ₑ(x ↦ Pred(x)) → (a : X) → Pred(a)
[∀ₑ]-elim (apx) (a) = (∀ₑ.quantification apx){a}

[∀ₑ]-elimₑ : ∀{X : Type}{Pred : X → Stmt} → (apx : ∀ₑ(x ↦ Pred(x))) → Pred(∀ₑ.element(apx))
[∀ₑ]-elimₑ apx = [∀ₑ]-elim apx(∀ₑ.element(apx))
