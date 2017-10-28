module Logic.Predicate {ℓ₁} {ℓ₂} where

open import Data
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Type{ℓ₂}

------------------------------------------
-- Existential quantification

data ∃ {X : Type} (body : X → Stmt) : Stmt where
  instance
    [∃]-intro : (x : X) → body(x) → ∃ body

[∃]-extract : ∀{X}{body} → ∃{X}(body) → X
[∃]-extract([∃]-intro(x)(_)) = x

[∃]-property : ∀{X}{body} → (e : ∃{X}(body)) → body([∃]-extract(e))
[∃]-property([∃]-intro(_)(p)) = p

[∃]-elim : ∀{X}{body}{Z : Stmt} → (∀{x : X} → body(x) → Z) → (∃{X} body) → Z
[∃]-elim (f) ([∃]-intro _ stmt) = f stmt

syntax ∃ {X} (λ x → f) = ∃[ x ∈ X ] f
-- syntax ∃ (λ x → f) = ∃[ x ] f
