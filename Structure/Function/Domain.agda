module Structure.Function.Domain lvl where

open import Functional
open import Logic(lvl)
open import Relator.Equals(lvl)

Injective : ∀{X Y : Set} → (X → Y) → Stmt
Injective {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

Surjective : ∀{X Y : Set} → (X → Y) → Stmt
Surjective {X} {Y} f = ∀{y : Y} → ∃{X}(λ x → f(x) ≡ y)

Bijective : ∀{X Y : Set} → (X → Y) → Stmt
Bijective f = (Injective f) ∧ (Surjective f)

domain : ∀{A B : Set} → (A → B) → Set
domain {A} {_} _ = A

codomain : ∀{A B : Set} → (A → B) → Set
codomain {_} {B} _ = B

restrict : ∀{A₁ A₂ B : Set}{_ : A₂ → A₁} → (A₁ → B) → (A₂ → B)
restrict {_} {_} {_} {tf} f = f ∘ tf

expand : ∀{A B₁ B₂ : Set}{_ : B₁ → B₂} → (A → B₁) → (A → B₂)
expand {_} {_} {_} {tf} f = tf ∘ f
