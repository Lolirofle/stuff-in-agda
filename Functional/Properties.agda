module Functional.Properties {ℓₗ} where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate{ℓₗ}
open import Functional
import      Relator.Equals
open import Relator.Equals.Theorems{ℓₗ}
open import Structure.Function.Domain {ℓₗ}
open import Type

module _ {ℓ₂ ℓ₃} where
  open Relator.Equals{ℓₗ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}

  -- The image/range of a function
  data Image {X : Type{ℓ₂}} {Y : Type{ℓ₃}} (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    image-intro : (x : X) → (y : Y) → ⦃ _ : f(x) ≡ y ⦄ → Image(f)
    -- TODO: image-intro : (x : X) → (y : Y) → .⦃ _ : ∃(x ↦ f(x) ≡ y) ⦄ → Image(f)

  image-apply : ∀{X}{Y}{f : X → Y} → X → (Image(f) → Y) → Y
  image-apply{X}{Y}{f} (x) (fimg) = fimg(image-intro (x) (f(x)) ⦃ [≡]-intro ⦄)

  image-value : ∀{X}{Y}{f : X → Y} → Image(f) → Y
  image-value(image-intro _ y) = y

  -- TODO: https://www.iis.sinica.edu.tw/~scm/2009/no-inverses-for-injective-but-non-surjective-functions/
  {-image-identity : ∀{X}{Y} → (f : X → Y) → ∃{_}{Image(f) → Y} (fid ↦ ∀{x} → (f(x) ≡ image-apply(x) (fid)))
  image-identity{X}{Y} (f) = [∃]-intro(witness) ⦃ proof ⦄ where
    witness : Image(f) → Y
    witness(image-intro x y ⦃ proof ⦄) = y

    postulate proof : ∀{x} → (f(x) ≡ image-apply(x) (witness))
-}
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
  open Relator.Equals{ℓₒ Lvl.⊔ ℓₗ}

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

  -- Every injective function has a left inverse with respect to function composition.
  -- TODO: Maybe also need to assume (∃x. x∈a)? That Inhabited(a). f: ∅→b is okay, but not g: b→∅. But that case should be impossible?
  {- [∘]-inverseₗ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ-value {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = [∃]-witness(f-injective{y})

    f⁻¹-proof : ∀{y} → ((f⁻¹ ∘ f)(y) ≡ id(y))
    f⁻¹-proof{y} = [∃]-proof(f-injective{y})
  -}

  -- TODO: https://math.stackexchange.com/questions/2049511/is-the-composition-of-two-injective-functions-injective/2049521
  [∘]-injective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Injective(f) → Injective(g) → Injective(f ∘ g)
  [∘]-injective{_}{_}{_} {f}{g} (injective-f) (injective-g) {x₁}{x₂} = (injective-g {x₁} {x₂}) ∘ (injective-f {g(x₁)} {g(x₂)})
  -- Alternative proof: [∘]-associativity {f⁻¹}{g⁻¹}{g}{f} becomes id by inverseₗ-value injective equivalence

  [∘]-injective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Injective(f ∘ g) → Injective(g)
  [∘]-injective-elim{_}{_}{_} {f}{g} (injective-fg) {x₁}{x₂} (gx₁gx₂) = injective-fg {x₁} {x₂} ([≡]-with(f) (gx₁gx₂))

  [∘]-surjective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Surjective(f) → Surjective(g) → Surjective(f ∘ g)
  [∘]-surjective{_}{_}{_} {f}{g} (surjective-f) (surjective-g) {y}
    with (surjective-f {y})
  ... | [∃]-intro (gx) ⦃ [≡]-intro ⦄
    with (surjective-g {gx})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄
    = [∃]-intro (x) ⦃ [≡]-intro ⦄

  [∘]-surjective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Surjective(f ∘ g) → Surjective(f)
  [∘]-surjective-elim{_}{_}{_} {f}{g} (surjective-fg) {y} with (surjective-fg {y})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄ = [∃]-intro (g(x)) ⦃ [≡]-intro ⦄

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

  inv-fn : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
  inv-fn = inv-fnₗ
