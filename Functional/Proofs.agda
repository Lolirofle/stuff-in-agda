module Functional.Proofs where

import      Lvl
open import Logic
open import Logic.Classical
open import Logic.Computability
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Functional.Names using (_⊜_)
open import Sets.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_ ; [≡]-with to [≡ₛ]-with ; Function to Functionₛ)
open import Sets.Setoid.Uniqueness
open import Structure.Relator.Function renaming (Function to RelatorFunction ; function to relatorFunction)
open import Structure.Relator.Properties
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Syntax.Transitivity
open import Type
open import Type.Empty

module _ {ℓₗ ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} (φ : A → B → Stmt{ℓₗ}) ⦃ totality : FunctionTotal(φ)⦄ ⦃ func : RelatorFunction(φ)⦄ where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- There is a function for a binary relation that is total and function-like.
  relation-function-existence : ∃(f ↦ ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y))
  relation-function-existence = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
    -- The function
    f : A → B
    f(x) = [∃]-witness(functionTotal(φ){x})

    -- Proof that the function returns the value that the binary relation defines the element from Y that an element from X is associated with.
    proof : ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y)
    proof{x}{y} = [↔]-intro l r where
      l : (f(x) ≡ y) ← φ(x)(y)
      l(φxy) = relatorFunction(φ) ([∃]-proof(functionTotal(φ){x})) (φxy)
        -- [∃]-proof(totality{x}) ∧ φ(x)(y)
        -- φ(x)([∃]-witness(totality{x})) ∧ φ(x)(y)
        -- [∃]-witness(totality{x}) = y
        -- f(x) = y

      r : (f(x) ≡ y) → φ(x)(y)
      r([≡]-intro) = [∃]-proof(functionTotal(φ){x})
        -- φ(x)(y)
        -- φ(x)([∃]-witness(totality{x}))

  -- Constructing a total function from a a binary operation with conditions.
  relation-function : A → B
  relation-function = [∃]-witness(relation-function-existence)

module _ {ℓₗ ℓₒ₁ ℓₒ₂} {X : Type{ℓₒ₁}} {Y : X → Type{ℓₒ₂}} {φ : (x : X) → Y(x) → Stmt{ℓₗ}} where
  -- Every binary predicate that have its first argument defined for all values
  -- have at least one choice function that can determine the second argument from the first.
  -- Proposition: ∀(X: Type)∀(Y: Type)∀(φ: X → Y → Stmt). (∀(x: X)∃(y: Y). φ(x)(y)) → (∃(choice: X → Y)∀(x: X). φ(x)(choice(x)))
  --   ∀(x: X)∃(y: Y). φ(x)(y) means that the predicate φ holds for every x and some y (which may depend on x). In other words: it associates every element in X with a subset of Y, a function (X → ℘(Y)).
  --   ∃(choice: X → Y)∀(x: X). φ(x)(choice(x)) means that there is a function that picks out a particular y.
  -- Note: This can be recognises as an equivalent variant of "Axiom of Choice" from set theory when working in classical logic.
  dependent-function-predicate-choice : (∀{x : X} → ∃{Obj = Y(x)}(y ↦ φ(x)(y))) → ∃{Obj = (x : X) → Y(x)}(choice ↦ ∀{x : X} → φ(x)(choice(x)))
  dependent-function-predicate-choice(function) = [∃]-intro (choice) ⦃ \{x} → proof{x} ⦄ where
    choice : (x : X) → Y(x)
    choice(x) = [∃]-witness(function{x})

    proof : ∀{x : X} → φ(x)(choice(x))
    proof{x} = [∃]-proof(function{x})

module _ {ℓₗ ℓₒ₁ ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} {φ : X → Y → Stmt{ℓₗ}} where
  function-predicate-choice : (∀{x} → ∃(y ↦ φ(x)(y))) → ∃{Obj = X → Y}(choice ↦ ∀{x} → φ(x)(choice(x)))
  function-predicate-choice = dependent-function-predicate-choice

{-
module _ {ℓₗ₁ ℓₗ₂ ℓₒ} {X : Type{ℓₒ}} {P : (X → Stmt{ℓₗ₁}) → Stmt{ℓₗ₂}} where
  standard-choice : (∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → (∃ P)) → ∃{Obj = (X → Stmt{ℓₗ₁}) → X}(f ↦ ∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → Q(f(Q)))
  standard-choice ep = [∃]-intro (choice) ⦃ \{x} → proof{x} ⦄ where
    choice : (X → Stmt{ℓₗ₁}) → X
    choice(R) = [∃]-witness(ep{R} (pr))

    proof : ∀{Q : X → Stmt{ℓₗ₁}} → P(Q) → Q(choice(Q))
    proof{Q} pq = [∃]-proof(surjective{x})
-}

module _ {ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} {f : A → B} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- A function is total
  -- ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality : FunctionTotal(x ↦ y ↦ f(x) ≡ y)
  FunctionTotal.proof(Function-totality) {x} = [∃]-intro(f(x)) ⦃ [≡]-intro ⦄

  instance
    -- A function is function-like.
    Function-function : Function(f)
    Function.proof(Function-function) {x} [≡]-intro = [≡]-intro

module _ {ℓₒ} where
  instance
    -- Identity function is a function.
    id-function : ∀{T} → ⦃ eq : Equiv(T) ⦄ → Function ⦃ eq ⦄ (id{ℓₒ}{T})
    Function.proof(id-function) = id

  instance
    -- Identity function is injective.
    id-injective : ∀{T} → ⦃ eq : Equiv(T) ⦄ → Injective ⦃ eq ⦄ (id{ℓₒ}{T})
    Injective.proof(id-injective) = id

  instance
    -- Identity function is surjective.
    id-surjective : ∀{T : Type{ℓₒ}} → ⦃ eq : Equiv(T) ⦄ → Surjective ⦃ eq ⦄ (id)
    Surjective.proof(id-surjective) {y} = [∃]-intro (y) ⦃ reflexivity(_≡ₛ_) ⦄

  instance
    -- Identity function is bijective.
    id-bijective : ∀{T} → ⦃ eq : Equiv(T) ⦄ → Bijective ⦃ eq ⦄ (id)
    id-bijective = injective-surjective-to-bijective(id)

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄} {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}}{c : Type{ℓₒ₃}}{d : Type{ℓₒ₄}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- Function composition is associative.
  [∘]-associativity : ∀{f : a → b}{g : b → c}{h : c → d} → ((h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f))
  [∘]-associativity = [≡]-intro

module _ {ℓₒ₁ ℓₒ₂} {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- Function composition has left identity element.
  [∘]-identityₗ : ∀{f : a → b} → (id ∘ f ≡ f)
  [∘]-identityₗ = [≡]-intro

  -- Function composition has right identity element.
  [∘]-identityᵣ : ∀{f : a → b} → (f ∘ id ≡ f)
  [∘]-identityᵣ = [≡]-intro

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {a : Type{ℓₒ₁}} ⦃ _ : Equiv(a) ⦄ {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv(c) ⦄ where
  -- The composition of injective functions is injective.
  -- TODO: https://math.stackexchange.com/questions/2049511/is-the-composition-of-two-injective-functions-injective/2049521
  -- Alternative proof: [∘]-associativity {f⁻¹}{g⁻¹}{g}{f} becomes id by inverseₗ-value injective equivalence
  [∘]-injective : ∀{f : b → c}{g : a → b} → ⦃ _ : Injective(f) ⦄ → ⦃ _ : Injective(g) ⦄ → Injective(f ∘ g)
  Injective.proof([∘]-injective {f = f}{g = g} ⦃ inj-f ⦄ ⦃ inj-g ⦄ ) {x₁}{x₂} = (injective(g) ⦃ inj-g ⦄ {x₁} {x₂}) ∘ (injective(f) ⦃ inj-f ⦄ {g(x₁)} {g(x₂)})

  -- RHS of composition is injective if the composition is injective.
  [∘]-injective-elim : ∀{f : b → c} → ⦃ _ : Function(f) ⦄ → ∀{g : a → b} → ⦃ _ : Injective(f ∘ g) ⦄ → Injective(g)
  Injective.proof([∘]-injective-elim {f = f}{g = g} ⦃ inj-fg ⦄) {x₁}{x₂} (gx₁gx₂) = injective(f ∘ g) ⦃ inj-fg ⦄ {x₁} {x₂} (function(f) (gx₁gx₂))

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {a : Type{ℓₒ₁}} {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv(c) ⦄ where
  -- The composition of surjective functions is surjective.
  [∘]-surjective : ∀{f : b → c} → ⦃ _ : Function(f) ⦄ → ∀{g : a → b} → ⦃ _ : Surjective(f) ⦄ → ⦃ _ : Surjective(g) ⦄ → Surjective(f ∘ g)
  Surjective.proof([∘]-surjective {f = f}{g = g}) {y}
    with (surjective(f) {y})
  ... | [∃]-intro (a) ⦃ fa≡y ⦄
    with (surjective(g) {a})
  ... | [∃]-intro (x) ⦃ gx≡a ⦄
    = [∃]-intro (x) ⦃ function(f) (gx≡a) 🝖 fa≡y ⦄

  -- LHS of composition is surjective if the composition is surjective.
  [∘]-surjective-elim : ∀{f : b → c}{g : a → b} → ⦃ _ : Surjective(f ∘ g) ⦄ → Surjective(f)
  Surjective.proof([∘]-surjective-elim {f = f}{g = g}) {y} with (surjective(f ∘ g) {y})
  ... | [∃]-intro (x) ⦃ fgx≡y ⦄ = [∃]-intro (g(x)) ⦃ fgx≡y ⦄

  -- Every injective function has a left inverse with respect to function composition.
  {-[∘]-inverseₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = 

    f⁻¹-proof : ∀{y} → ((f ∘ f⁻¹)(y) ≡ id(y))
    f⁻¹-proof{y} = 
  -}

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {a : Type{ℓₒ₁}} ⦃ _ : Equiv(a) ⦄ {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv(c) ⦄ where
  -- The composition of bijective functions is bijective.
  [∘]-bijective : ∀{f : b → c} → ⦃ _ : Function(f) ⦄ → ∀{g : a → b} → ⦃ _ : Bijective(f) ⦄ → ⦃ _ : Bijective(g) ⦄ → Bijective(f ∘ g)
  [∘]-bijective {f = f} ⦃ func-f ⦄ {g} ⦃ bij-f ⦄ ⦃ bij-g ⦄ =
    injective-surjective-to-bijective(f ∘ g)
      ⦃ [∘]-injective {f = f}{g = g}
        ⦃ bijective-to-injective(f) ⦃ bij-f ⦄ ⦄
        ⦃ bijective-to-injective(g) ⦃ bij-g ⦄ ⦄
      ⦄
      ⦃ [∘]-surjective {f = f} ⦃ func-f ⦄ {g = g}
        ⦃ bijective-to-surjective(f) ⦃ bij-f ⦄ ⦄
        ⦃ bijective-to-surjective(g) ⦃ bij-g ⦄ ⦄
      ⦄

  -- The composition of functions is a function.
  [∘]-function : ∀{f : b → c}{g : a → b} → ⦃ _ : Function(f) ⦄ → ⦃ _ : Function(g) ⦄ → Function(f ∘ g)
  Function.proof([∘]-function {f = f}{g = g} ⦃ func-f ⦄ ⦃ func-g ⦄ ) {x₁}{x₂} = (function(f) ⦃ func-f ⦄ {g(x₁)} {g(x₂)}) ∘ (function(g) ⦃ func-g ⦄ {x₁} {x₂})

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv(B) ⦄ where
  private
    _⊜AB_ = _⊜_ {A = A}{B} ⦃ eqB ⦄
    _⊜BA_ = _⊜_ {A = B}{A} ⦃ eqA ⦄
    _⊜AA_ = _⊜_ {A = A}{A} ⦃ eqA ⦄
    _⊜BB_ = _⊜_ {A = B}{B} ⦃ eqB ⦄

{-
  -- Every injective function has a left inverse with respect to function composition.
  -- TODO: Maybe also need to assume (∃x. x∈a)? That Inhabited(a). f: ∅→b is okay, but not g: b→∅. But that case should be impossible?
  [∘]-inverseₗ : ∀{f : A → B} → ⦃ _ : Injective(f) ⦄ → ⦃ (◊ A) ⦄ → ⦃ _ : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ → ∃(g ↦ g ∘ f ⊜AA id)
  [∘]-inverseₗ {f} ⦃ f-injective ⦄ ⦃ intro ⦃ a ⦄ ⦄ ⦃ classical ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : B → A
    f⁻¹(y) with excluded-middle{P = ∃(x ↦ Equiv._≡_ eqB (f(x)) y)}
    f⁻¹ y | [∨]-introₗ ([∃]-intro x) = x
    f⁻¹ y | [∨]-introᵣ _             = a

    test : ⦃ _ : Functionₛ(f⁻¹) ⦄ → ∀{y} → (([∃]-intro x) : ∃(x ↦ Equiv._≡_ eqB (f(x)) y)) → (Equiv._≡_ eqA (f⁻¹(y)) x)
    test ⦃ func-f⁻¹ ⦄ {y} ([∃]-intro x ⦃ fxy ⦄) = {![≡ₛ]-with(f⁻¹) fxy!}

    -- TODO: How to split the cases in the proof here?
    f⁻¹-proof : (f⁻¹ ∘ f ⊜ id)
    f⁻¹-proof{x} = {!!}
-}

  -- Every surjective function has a right inverse with respect to function composition.
  -- Note: Equivalent to axiom of choice from set theory when formulated in classical logic.
  [∘]-inverseᵣ : ∀{f : A → B} → ⦃ _ : Surjective(f) ⦄ → ∃{Obj = B → A}(g ↦ f ∘ g ⊜BB id)
  [∘]-inverseᵣ {f} ⦃ f-surjective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : B → A
    f⁻¹(y) = [∃]-witness(surjective(f) {y})

    f⁻¹-proof : (f ∘ f⁻¹ ⊜ id)
    f⁻¹-proof{y} = [∃]-proof(surjective(f) {y})

  -- invᵣ(f) is one of the right inverse functions of a surjective function f.
  invᵣ : (f : A → B) → ⦃ _ : Surjective(f) ⦄ → (B → A)
  invᵣ(f) = [∃]-witness([∘]-inverseᵣ{f = f})

  -- inv(f) is the inverse function of a bijective function f.
  inv : (f : A → B) → ⦃ _ : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (B → A)
  inv(f) ⦃ bij ⦄ = invᵣ(f) ⦃ bijective-to-surjective(f) ⦃ bij ⦄ ⦄

  -- invᵣ is a right inverse function to a surjective f.
  invᵣ-inverseᵣ : ∀{f} → ⦃ _ : Surjective(f) ⦄ → (f ∘ invᵣ(f) ⊜ id)
  invᵣ-inverseᵣ{f} = [∃]-proof([∘]-inverseᵣ{f = f})

  -- inv is a right inverse function to a bijective f.
  inv-inverseᵣ : ∀{f} → ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (f ∘ inv(f) ⦃ bij ⦄ ⊜ id)
  inv-inverseᵣ{f} ⦃ bij ⦄ = invᵣ-inverseᵣ{f} ⦃ bijective-to-surjective(f) ⦃ bij ⦄ ⦄

  -- inv is a left inverse function to a bijective f.
  inv-inverseₗ : ∀{f} → ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (inv(f) ⦃ bij ⦄ ∘ f ⊜AA id)
  inv-inverseₗ{f} ⦃ bij ⦄ = [∃!]-existence-eq-any (bijective(f) ⦃ bij ⦄) (reflexivity(_≡ₛ_))

  module _ {f : A → B} ⦃ func : Function ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ ⦃ surj : Surjective ⦃ eqB ⦄ (f) ⦄ where
    -- invᵣ(f) is injective when f is a function and is surjective.
    invᵣ-injective : Injective(invᵣ f ⦃ surj ⦄)
    Injective.proof(invᵣ-injective) {x₁}{x₂} (invᵣfx₁≡invᵣfx₂) =
      symmetry(_≡ₛ_) (invᵣ-inverseᵣ{f} ⦃ surj ⦄ {x₁})
      🝖 function(f) ⦃ func ⦄ {invᵣ f ⦃ surj ⦄ (x₁)} {invᵣ f ⦃ surj ⦄ (x₂)} (invᵣfx₁≡invᵣfx₂)
      🝖 invᵣ-inverseᵣ{f} ⦃ surj ⦄ {x₂}

  module _ {f : A → B} ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ where
    -- inv(f) is surjective when f is bijective.
    inv-surjective : Surjective ⦃ eqA ⦄ (inv(f) ⦃ bij ⦄)
    Surjective.proof(inv-surjective) {x} = [∃]-intro(f(x)) ⦃ inv-inverseₗ {f} ⦃ bij ⦄ ⦄

  module _ {f : A → B} ⦃ func : Function ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ where
    -- inv(f) is a function when f is a function and is bijective.
    inv-function : Function ⦃ eqB ⦄ ⦃ eqA ⦄ (inv(f) ⦃ bij ⦄)
    Function.proof(inv-function) {x₁}{x₂} (x₁≡x₂) =
      injective(f) ⦃ bijective-to-injective(f) ⦃ bij ⦄ ⦄ {inv f ⦃ bij ⦄ (x₁)} {inv f ⦃ bij ⦄ (x₂)}
        (
          inv-inverseᵣ{f} ⦃ bij ⦄ {x₁}
          🝖 x₁≡x₂
          🝖 symmetry(_≡ₛ_) (inv-inverseᵣ{f} ⦃ bij ⦄ {x₂})
        )

    -- inv(f) is injective when f is a function and is bijective.
    inv-injective : Injective(inv f ⦃ bij ⦄)
    Injective.proof(inv-injective) {x₁}{x₂} (invfx₁≡invfx₂) =
      symmetry(_≡ₛ_) (inv-inverseᵣ{f} ⦃ bij ⦄ {x₁})
      🝖 function(f) ⦃ func ⦄ {inv f ⦃ bij ⦄ (x₁)} {inv f ⦃ bij ⦄ (x₂)} (invfx₁≡invfx₂)
      🝖 inv-inverseᵣ{f} ⦃ bij ⦄ {x₂}

    -- inv(f) is bijective when f is a function and is bijective.
    inv-bijective : Bijective(inv(f) ⦃ bij ⦄)
    inv-bijective = injective-surjective-to-bijective(inv(f) ⦃ bij ⦄) ⦃ inv-injective ⦄ ⦃ inv-surjective ⦃ bij ⦄ ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  swap-involution : ∀{f : X → Y → Z} → (swap(swap(f)) ≡ f)
  swap-involution = [≡]-intro

  s-combinator-const-id : (s-combinator{X = X}{Y → X}{X} const const ≡ id)
  s-combinator-const-id = [≡]-intro

{- TODO: Maybe this is unprovable because types. https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog https://plato.stanford.edu/entries/axiom-choice/choice-and-type-theory.html https://en.wikipedia.org/wiki/Diaconescu%27s_theorem
module _ {fn-ext : FunctionExtensionality} where
  open import Functional.Names
  open import Data.Boolean

  function-extensionality-to-classical : ∀{P} → (P ∨ (¬ P))
  function-extensionality-to-classical{P} = where
    A : Bool → Stmt
    A(x) = (P ∨ (x ≡ 𝐹))

    B : Bool → Stmt
    B(x) = (P ∨ (x ≡ 𝑇))

    C : (Bool → Stmt) → Stmt
    C(F) = (F ⊜ A) ∨ (F ⊜ B)
-}
