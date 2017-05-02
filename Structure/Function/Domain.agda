module Structure.Function.Domain {l₁} {l₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Relator.Equals{l₁}{l₂}
open import Type{l₁}

Injective : ∀{X Y : Type} → (X → Y) → Stmt
Injective {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

Surjective : ∀{X Y : Type} → (X → Y) → Stmt
Surjective {X} {Y} f = ∀{y : Y} → ∃{X}(x ↦ (f(x) ≡ y))

Bijective : ∀{X Y : Type} → (X → Y) → Stmt
Bijective f = (Injective f) ∧ (Surjective f)

domain : ∀{A B : Type} → (A → B) → Type
domain {A} {_} _ = A

codomain : ∀{A B : Type} → (A → B) → Type
codomain {_} {B} _ = B

restrict : ∀{A₁ A₂ B : Type}{_ : A₂ → A₁} → (A₁ → B) → (A₂ → B)
restrict {_} {_} {_} {tf} f = f ∘ tf

expand : ∀{A B₁ B₂ : Type}{_ : B₁ → B₂} → (A → B₁) → (A → B₂)
expand {_} {_} {_} {tf} f = tf ∘ f
