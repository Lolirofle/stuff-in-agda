module Functional.Properties {ℓₗ} where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate{ℓₗ}
open import Functional
open import Relator.Equals{ℓₗ}
open import Relator.Equals.Theorems{ℓₗ}
open import Structure.Function.Domain {ℓₗ}
open import Type

-- Every binary predicate that have its first argument defined for all values
-- have at least one choice function that can determine the second argument from the first.
-- Proposition: ∀(X: Type)∀(Y: Type)∀(φ: X → Y → Stmt). (∀(x: X)∃(y: Y). φ(x)(y)) → (∃(choice: X → Y)∀(x: X). φ(x)(choice(x)))
--   ∀(x: X)∃(y: Y). φ(x)(y) means that the predicate φ holds for every x and some y (which depends on x).
--   ∃(choice: X → Y)∀(x: X). φ(x)(choice(x)) means that there is a function that picks out this y (which depends on x).
surjective-choice : ∀{ℓₒ₁ ℓₒ₂}{X : Type{ℓₒ₁}}{Y : X → Type{ℓₒ₂}}{φ : (x : X) → Y(x) → Stmt} → (∀{x : X} → ∃{_}{Y(x)}(y ↦ φ(x)(y))) → ∃{_}{(x : X) → Y(x)}(choice ↦ ∀{x : X} → φ(x)(choice(x)))
surjective-choice{_}{_} {X}{Y}{φ} (surjective) = [∃]-intro (choice) ⦃ \{x} → proof{x} ⦄ where
  choice : ∀(x : X) → Y(x)
  choice(x) = [∃]-witness(surjective{x})

  proof : ∀{x : X} → φ(x)(choice(x))
  proof{x} = [∃]-proof(surjective{x})

module _ {ℓₒ} where
  Function-totality : ∀{A B : Type{ℓₒ}}{f : A → B} → ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality{_}{_} {f}{x} = [∃]-intro(f(x)) ⦃ [≡]-intro ⦄

  Function-function : ∀{A B : Type{ℓₒ}}{f : A → B} → ∀{x₁ x₂} → (x₁ ≡ x₂) → (f(x₁) ≡ f(x₂))
  Function-function{_}{_} {f}{x} [≡]-intro = [≡]-intro

  instance
    id-injective : ∀{T} → Injective(id{ℓₒ}{T})
    id-injective [≡]-intro = [≡]-intro

  instance
    id-surjective : ∀{T : Type{ℓₒ}} → Surjective(id{_}{T})
    id-surjective {_}{y} = [∃]-intro (y) ⦃ [≡]-intro ⦄

  instance
    id-bijective : ∀{T} → Bijective(id{_}{T})
    id-bijective = [∧]-intro(id-injective)(id-surjective)

  [∘]-associativity : ∀{a b c d : Type{ℓₒ}}{f : a → b}{g : b → c}{h : c → d} → ((h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f))
  [∘]-associativity = [≡]-intro

  [∘]-identityₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → (id ∘ f ≡ f)
  [∘]-identityₗ = [≡]-intro

  [∘]-identityᵣ : ∀{a b : Type{ℓₒ}}{f : a → b} → (f ∘ id ≡ f)
  [∘]-identityᵣ = [≡]-intro

  {- -- Every injective function has a left inverse with respect to function composition.
  -- TODO: Maybe also need to assume (∃x. x∈a)? That Inhabited(a). f: ∅→b is okay, but not g: b→∅
  [∘]-inverseₗ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ-value {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = [∃]-witness(f-surjective{y})

    f⁻¹-proof : ∀{y} → ((f⁻¹ ∘ f)(y) ≡ id(y))
    f⁻¹-proof{y} = [∃]-proof(f-surjective{y})
  -}

  -- Every surjective function has a right inverse with respect to function composition.
  -- Note: Equivalent to axiom of choice from set theory.
  [∘]-inverseᵣ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Surjective(f) ⦄ → ∃(g ↦ ∀{x} → ((f ∘ g)(x) ≡ id(x)))
  [∘]-inverseᵣ-value {a}{b} {f} ⦃ f-surjective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = [∃]-witness(f-surjective{y})

    f⁻¹-proof : ∀{y} → ((f ∘ f⁻¹)(y) ≡ id(y))
    f⁻¹-proof{y} = [∃]-proof(f-surjective{y})

  -- TODO: Are these really provable?
  postulate [∘]-inverseₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ g ∘ f ≡ id)
  postulate [∘]-inverseᵣ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ f ∘ g ≡ id)

  inv-fnₗ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
  inv-fnₗ (f) = [∃]-witness([∘]-inverseₗ{_}{_}{f})

  inv-fnᵣ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
  inv-fnᵣ (f) = [∃]-witness([∘]-inverseᵣ{_}{_}{f})

  inv-fn : ∀{a} → (f : a → a) → ⦃ _ : Bijective(f) ⦄ → (a → a)
  inv-fn = inv-fnₗ
