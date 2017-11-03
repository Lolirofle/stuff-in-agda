module Logic.Predicate {ℓ₁} {ℓ₂} where

open import Data
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}

------------------------------------------
-- Existential quantification

record ∃ {X : Type} (Pred : X → Stmt) : Stmt where
  constructor [∃]-intro
  field
    element   : X
    predicate : Pred(element)

[∃]-extract : ∀{X}{Pred} → ∃{X}(Pred) → X
[∃]-extract([∃]-intro(x)(_)) = x

[∃]-property : ∀{X}{Pred} → (e : ∃{X}(Pred)) → Pred([∃]-extract(e))
[∃]-property([∃]-intro(_)(p)) = p

[∃]-elim : ∀{X}{Pred}{Z : Stmt} → (∀{x : X} → Pred(x) → Z) → (∃{X} Pred) → Z
[∃]-elim (f) ([∃]-intro _ stmt) = f stmt

-- syntax ∃ {X} (λ x → f) = ∃[ x ∊ X ] f
-- syntax ∃     (λ x → f) = ∃[ x ] f

∀ₗ : ∀{X : Type} → (Pred : X → Stmt) → Stmt
∀ₗ (Pred) = (∀{x} → Pred(x))

[∀]-elim : ∀{X : Type}{Pred : X → Stmt} → (∀{x : X} → Pred(x)) → ∀{a : X} → Pred(a)
[∀]-elim p{a} = p{a}
