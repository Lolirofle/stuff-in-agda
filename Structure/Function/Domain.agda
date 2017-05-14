module Structure.Function.Domain {l₁} {l₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Relator.Equals{l₁}{l₂}
open import Type{l₁}

-- Definition of injectivity for a function
Injective : ∀{X Y : Type} → (X → Y) → Stmt
Injective {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

-- Definition of surjectivity for a function
Surjective : ∀{X Y : Type} → (X → Y) → Stmt
Surjective {X} {Y} f = ∀{y : Y} → ∃{X}(x ↦ (f(x) ≡ y))

-- Definition of bijectivity for a function
Bijective : ∀{X Y : Type} → (X → Y) → Stmt
Bijective f = (Injective f) ∧ (Surjective f)

-- Returns the domain of a function
domain : ∀{A B : Type} → (A → B) → Type
domain {A} {_} _ = A

-- Returns the codomain of a function
codomain : ∀{A B : Type} → (A → B) → Type
codomain {_} {B} _ = B

-- Returns a function with a smaller domain
restrict : ∀{A₁ A₂ B : Type}{_ : A₂ → A₁} → (A₁ → B) → (A₂ → B)
restrict {_} {_} {_} {tf} f = f ∘ tf

-- Returns a function with a larger codomain
expand : ∀{A B₁ B₂ : Type}{_ : B₁ → B₂} → (A → B₁) → (A → B₂)
expand {_} {_} {_} {tf} f = tf ∘ f

-- Definition of a fixed point for a function
FixPoint : ∀{T : Type} → (T → T) → T → Stmt
FixPoint f(x) = (f(x) ≡ x)

-- Definition of an inverse function for a function
Inverse : ∀{A B : Type} → (A → B) → (B → A) → Stmt
Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (f⁻¹(y) ≡ x))

-- Definition of an inverse function for a function
InverseId : ∀{A B : Type} → (A → B) → (B → A) → Stmt
InverseId f f⁻¹ = ((f ∘ f⁻¹) ≡ id) -- TODO: Prove equivalence of this and above

-- Definition of an constant function
Constant : ∀{A B : Type} → (A → B) → Stmt
Constant f = (∃(y ↦ ∀{x} → f(x) ≡ y))
