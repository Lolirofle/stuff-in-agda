module Logic.Predicate {l₁} {l₂} where

open import Data
import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Type{l₂}

------------------------------------------
-- Existential quantification

data ∃ {X : Type} (body : X → Stmt) : Stmt where
  [∃]-intro : (x : X) → body(x) → ∃ body

[∃]-extract : ∀{X}{body} → ∃{X}(body) → X
[∃]-extract([∃]-intro(x)(_)) = x

[∃]-elim : ∀{X}{body}{Z : Stmt} → (∀{x : X} → body(x) → Z) → (∃{X} body) → Z
[∃]-elim (f) ([∃]-intro _ stmt) = f stmt

syntax ∃ {X} (λ x → f) = ∃[ x ∈ X ] f
-- syntax ∃ (λ x → f) = ∃[ x ] f
