module Logic.Predicate {l₁} {l₂} where

open import Data
import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Type{l₁}

------------------------------------------
-- Existential quantification

data ∃ {X : Type} (body : X → Stmt) : Stmt where
  [∃]-intro : (x : X) → body(x) → ∃ body

[∃]-elim : ∀{X body}{Z : Stmt} → ((∀{x : X} → body(x) → Z) ⨯ (∃ {X} body)) → Z
[∃]-elim(f , ([∃]-intro _ stmt)) = f stmt

-- syntax ∃ {X} (x ↦ f) = ∃[ x ∈ X ] f

-- TODO
-- testExists : ∀{T : Type}{f : T → Type} → (∃[ x ∈ T ] (f x)) → (∃ {T} (x ↦ f x))
-- testExists x = x
