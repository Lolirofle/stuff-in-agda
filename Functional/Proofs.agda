module Functional.Proofs {ℓₗ} where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate{ℓₗ}
open import Functional
import      Relator.Equals
open import Relator.Equals.Proofs{ℓₗ}
open import Structure.Relator.Function{ℓₗ}
open import Structure.Function.Domain{ℓₗ}
open import Type

module _ {ℓₒ₁ ℓₒ₂} where
  open Relator.Equals{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}

  -- There is a function for a binary relation that is total and function-like.
  function-existence : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt) → ⦃ _ : FunctionTotal(φ)⦄ → ⦃ _ : Function(φ)⦄ → ∃(f ↦ ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y))
  function-existence{A}{B} (φ) ⦃ totality ⦄ ⦃ function ⦄ = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
    -- The function
    f : A → B
    f(x) = [∃]-witness(totality{x})

    -- Proof that the function returns the value that the binary relation defines the element from Y that an element from X is associated with.
    proof : ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y)
    proof{x}{y} = [↔]-intro l r where
      l : (f(x) ≡ y) ← φ(x)(y)
      l(φxy) = function([∃]-proof(totality{x})) (φxy)
        -- [∃]-proof(totality{x}) ∧ φ(x)(y)
        -- φ(x)([∃]-witness(totality{x})) ∧ φ(x)(y)
        -- [∃]-witness(totality{x}) = y
        -- f(x) = y

      r : (f(x) ≡ y) → φ(x)(y)
      r([≡]-intro) = [∃]-proof(totality{x})
        -- φ(x)(y)
        -- φ(x)([∃]-witness(totality{x}))

  -- Constructing a total function from a a binary operation with conditions.
  function : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt) → ⦃ _ : FunctionTotal(φ)⦄ → ⦃ _ : Function(φ)⦄ → (A → B)
  function(φ) ⦃ totality ⦄ ⦃ function ⦄ = [∃]-witness(function-existence(φ) ⦃ totality ⦄ ⦃ function ⦄)

-- Every binary predicate that have its first argument defined for all values
-- have at least one choice function that can determine the second argument from the first.
-- Proposition: ∀(X: Type)∀(Y: Type)∀(φ: X → Y → Stmt). (∀(x: X)∃(y: Y). φ(x)(y)) → (∃(choice: X → Y)∀(x: X). φ(x)(choice(x)))
--   ∀(x: X)∃(y: Y). φ(x)(y) means that the predicate φ holds for every x and some y (which may depend on x). In other words: it associates every element in X with a subset of Y, a function (X → ℘(Y)).
--   ∃(choice: X → Y)∀(x: X). φ(x)(choice(x)) means that there is a function that picks out a particular y.
-- Note: Some may recognise this as an equivalent variant of "Axiom of Choice" from set theory.
surjective-choice : ∀{ℓₒ₁ ℓₒ₂}{X : Type{ℓₒ₁}}{Y : X → Type{ℓₒ₂}}{φ : (x : X) → Y(x) → Stmt} → (∀{x : X} → ∃{_}{Y(x)}(y ↦ φ(x)(y))) → ∃{_}{(x : X) → Y(x)}(choice ↦ ∀{x : X} → φ(x)(choice(x)))
surjective-choice{_}{_} {X}{Y}{φ} (surjective) = [∃]-intro (choice) ⦃ \{x} → proof{x} ⦄ where
  choice : ∀(x : X) → Y(x)
  choice(x) = [∃]-witness(surjective{x})

  proof : ∀{x : X} → φ(x)(choice(x))
  proof{x} = [∃]-proof(surjective{x})

module _ {ℓₒ} where
  open Relator.Equals{ℓₒ Lvl.⊔ ℓₗ}

  -- A function is total
  -- ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality : ∀{A B : Type{ℓₒ}}{f : A → B} → FunctionTotal(x ↦ y ↦ f(x) ≡ y)
  Function-totality{_}{_} {f}{x} = [∃]-intro(f(x)) ⦃ [≡]-intro ⦄

  -- A function is function-like.
  Function-functionlike : ∀{A B : Type{ℓₒ}}{f : A → B} → ∀{x₁ x₂} → (x₁ ≡ x₂) → (f(x₁) ≡ f(x₂))
  Function-functionlike{_}{_} {f}{x} [≡]-intro = [≡]-intro

  instance
    -- Identity function is injective.
    id-injective : ∀{T} → Injective(id{ℓₒ}{T})
    id-injective [≡]-intro = [≡]-intro

  instance
    -- Identity function is surjective.
    id-surjective : ∀{T : Type{ℓₒ}} → Surjective{ℓₒ}{ℓₒ}(id{_}{T})
    id-surjective {_}{y} = [∃]-intro (y) ⦃ [≡]-intro ⦄

  instance
    -- Identity function is bijective.
    id-bijective : ∀{T} → Bijective{ℓₒ}{ℓₒ}(id{_}{T})
    id-bijective = [∧]-intro(id-injective)(id-surjective)

  -- Function composition is associative.
  [∘]-associativity : ∀{a b c d : Type{ℓₒ}}{f : a → b}{g : b → c}{h : c → d} → ((h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f))
  [∘]-associativity = [≡]-intro

  -- Function composition has left identity element.
  [∘]-identityₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → (id ∘ f ≡ f)
  [∘]-identityₗ = [≡]-intro

  -- Function composition has right identity element.
  [∘]-identityᵣ : ∀{a b : Type{ℓₒ}}{f : a → b} → (f ∘ id ≡ f)
  [∘]-identityᵣ = [≡]-intro

  -- Every injective function has a left inverse with respect to function composition.
  -- TODO: Maybe also need to assume (∃x. x∈a)? That Inhabited(a). f: ∅→b is okay, but not g: b→∅. But that case should be impossible?
  {- [∘]-inverseₗ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ⦃ _ : Inhabited(a) ⦄ → ⦃ _ : ∀{y} → Decidable(Image-in(f)(y)) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ-value {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = [∃]-witness(f-injective{y})

    f⁻¹-proof : ∀{y} → ((f⁻¹ ∘ f)(y) ≡ id(y))
    f⁻¹-proof{y} = [∃]-proof(f-injective{y})
  -}

  -- Composition of injective functions are injective.
  -- TODO: https://math.stackexchange.com/questions/2049511/is-the-composition-of-two-injective-functions-injective/2049521
  -- Alternative proof: [∘]-associativity {f⁻¹}{g⁻¹}{g}{f} becomes id by inverseₗ-value injective equivalence
  [∘]-injective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Injective(f) → Injective(g) → Injective(f ∘ g)
  [∘]-injective{_}{_}{_} {f}{g} (injective-f) (injective-g) {x₁}{x₂} = (injective-g {x₁} {x₂}) ∘ (injective-f {g(x₁)} {g(x₂)})

  -- RHS of composition is injective if the composition is injective.
  [∘]-injective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Injective(f ∘ g) → Injective(g)
  [∘]-injective-elim{_}{_}{_} {f}{g} (injective-fg) {x₁}{x₂} (gx₁gx₂) = injective-fg {x₁} {x₂} ([≡]-with(f) (gx₁gx₂))

  -- Composition of surjective functions are surjective.
  [∘]-surjective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Surjective{ℓₒ}{ℓₒ}(f) → Surjective{ℓₒ}{ℓₒ}(g) → Surjective{ℓₒ}{ℓₒ}(f ∘ g)
  [∘]-surjective{_}{_}{_} {f}{g} (surjective-f) (surjective-g) {y}
    with (surjective-f {y})
  ... | [∃]-intro (gx) ⦃ [≡]-intro ⦄
    with (surjective-g {gx})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄
    = [∃]-intro (x) ⦃ [≡]-intro ⦄

  -- LHS of composition is surjective if the composition is surjective.
  [∘]-surjective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → Surjective{ℓₒ}{ℓₒ}(f ∘ g) → Surjective{ℓₒ}{ℓₒ}(f)
  [∘]-surjective-elim{_}{_}{_} {f}{g} (surjective-fg) {y} with (surjective-fg {y})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄ = [∃]-intro (g(x)) ⦃ [≡]-intro ⦄

  -- Every injective function has a left inverse with respect to function composition.
  {-[∘]-inverseₗ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ-value {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = 

    f⁻¹-proof : ∀{y} → ((f ∘ f⁻¹)(y) ≡ id(y))
    f⁻¹-proof{y} = 
  -}

  -- Every surjective function has a right inverse with respect to function composition.
  -- Note: Equivalent to axiom of choice from set theory.
  [∘]-inverseᵣ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Surjective{ℓₒ}{ℓₒ}(f) ⦄ → ∃(g ↦ ∀{x} → ((f ∘ g)(x) ≡ id(x)))
  [∘]-inverseᵣ-value {a}{b} {f} ⦃ f-surjective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = [∃]-witness(f-surjective{y})

    f⁻¹-proof : ∀{y} → ((f ∘ f⁻¹)(y) ≡ id(y))
    f⁻¹-proof{y} = [∃]-proof(f-surjective{y})

  -- TODO: Are these really provable?
  -- postulate [∘]-inverseₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ g ∘ f ≡ id)
  -- postulate [∘]-inverseᵣ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ f ∘ g ≡ id)

  -- TODO: 
  -- inv-fnₗ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
  -- inv-fnₗ (f) = [∃]-witness([∘]-inverseₗ{_}{_}{f})

  inv-fnᵣ : ∀{a b} → (f : a → b) → ⦃ _ : Surjective{ℓₒ}{ℓₒ}(f) ⦄ → (b → a)
  inv-fnᵣ (f) = [∃]-witness([∘]-inverseᵣ-value{_}{_}{f})

  inv-fn : ∀{a b} → (f : a → b) → ⦃ _ : Bijective{ℓₒ}{ℓₒ}(f) ⦄ → (b → a)
  inv-fn (f) ⦃ [∧]-intro inj surj ⦄ = inv-fnᵣ (f) ⦃ surj ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  open Relator.Equals{ℓₗ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}

  swap-involution : ∀{f : X → Y → Z} → (swap(swap(f)) ≡ f)
  swap-involution = [≡]-intro
