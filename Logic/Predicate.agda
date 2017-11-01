module Logic.Predicate {ℓ₁} {ℓ₂} where

open import Data
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}

------------------------------------------
-- Existential quantification

data ∃ {X : Type} (Pred : X → Stmt) : Stmt where
  instance
    [∃]-intro : (x : X) → Pred(x) → ∃ Pred

[∃]-extract : ∀{X}{Pred} → ∃{X}(Pred) → X
[∃]-extract([∃]-intro(x)(_)) = x

[∃]-property : ∀{X}{Pred} → (e : ∃{X}(Pred)) → Pred([∃]-extract(e))
[∃]-property([∃]-intro(_)(p)) = p

[∃]-elim : ∀{X}{Pred}{Z : Stmt} → (∀{x : X} → Pred(x) → Z) → (∃{X} Pred) → Z
[∃]-elim (f) ([∃]-intro _ stmt) = f stmt

syntax ∃ {X} (λ x → f) = ∃[ x ∈ X ] f
-- syntax ∃ (λ x → f) = ∃[ x ] f

[∀]-elim : ∀{X : Stmt}{Pred : X → Stmt} → (∀{x : X} → Pred(x)) → ∀{a : X} → Pred(a)
[∀]-elim p{a} = p{a}

module PredicateTheorems where
  open import Functional

  [∀]-to-[∃] : ∀{X}{P : X → Stmt} → (∀{x} → P(x)) → ¬(∃(x ↦ ¬(P(x))))
  [∀]-to-[∃]{P} (p)(ep) = [∃]-elim(\{a} → npa ↦ npa(p{a}))(ep)
