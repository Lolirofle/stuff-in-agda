module Functional.Proofs where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Functional.Names using (_⊜_)
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Sets.Setoid.Uniqueness
open import Structure.Relator.Function renaming (Function to RelatorFunction ; function to relatorFunction)
open import Structure.Relator.Properties
open import Structure.Function.Domain renaming (function to function-proof)
open import Structure.Function.Domain.Proofs
open import Type

module _ {ℓₗ ℓₒ₁ ℓₒ₂} where
  -- There is a function for a binary relation that is total and function-like.
  function-existence : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt{ℓₗ}) → ⦃ _ : FunctionTotal(φ)⦄ → ⦃ _ : RelatorFunction(φ)⦄ → ∃(f ↦ ∀{x}{y} → (f(x) ≡ y) ↔ φ(x)(y))
  function-existence{A}{B} (φ) ⦃ FunctionTotal.intro totality ⦄ ⦃ RelatorFunction.intro function ⦄ = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
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
  function : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} → (φ : A → B → Stmt{ℓₗ}) → ⦃ _ : FunctionTotal(φ)⦄ → ⦃ _ : RelatorFunction(φ)⦄ → (A → B)
  function(φ) ⦃ totality ⦄ ⦃ function ⦄ = [∃]-witness(function-existence(φ) ⦃ totality ⦄ ⦃ function ⦄)

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

module _ {ℓₒ} where
  -- A function is total
  -- ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality : ∀{A B : Type{ℓₒ}}{f : A → B} → FunctionTotal(x ↦ y ↦ f(x) ≡ y)
  FunctionTotal.proof(Function-totality{_}{_} {f}) {x} = [∃]-intro(f(x)) ⦃ [≡]-intro ⦄

  -- A function is function-like.
  Function-functionlike : ∀{A B : Type{ℓₒ}}{f : A → B} → ∀{x₁ x₂} → (x₁ ≡ x₂) → (f(x₁) ≡ f(x₂))
  Function-functionlike{_}{_} {f}{x} [≡]-intro = [≡]-intro

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
  instance
    [∘]-injective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Injective(f) ⦄ → ⦃ _ : Injective(g) ⦄ → Injective(f ∘ g)
    Injective.proof([∘]-injective {f = f}{g = g} ⦃ inj-f ⦄ ⦃ inj-g ⦄ ) {x₁}{x₂} = (injective(g) ⦃ inj-g ⦄ {x₁} {x₂}) ∘ (injective(f) ⦃ inj-f ⦄ {g(x₁)} {g(x₂)})

  -- RHS of composition is injective if the composition is injective.
  [∘]-injective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Injective(f ∘ g) ⦄ → Injective(g)
  Injective.proof([∘]-injective-elim {f = f}{g = g} ⦃ inj-fg ⦄) {x₁}{x₂} (gx₁gx₂) = injective(f ∘ g) ⦃ inj-fg ⦄ {x₁} {x₂} ([≡]-with(f) (gx₁gx₂))

  -- Composition of surjective functions are surjective.
  [∘]-surjective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Surjective{ℓₒ}{ℓₒ}(f) ⦄ → ⦃ _ : Surjective{ℓₒ}{ℓₒ}(g) ⦄ → Surjective{ℓₒ}{ℓₒ}(f ∘ g)
  Surjective.proof([∘]-surjective {f = f}{g = g}) {y}
    with (surjective(f) {y})
  ... | [∃]-intro (gx) ⦃ [≡]-intro ⦄
    with (surjective(g) {gx})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄
    = [∃]-intro (x) ⦃ [≡]-intro ⦄

  -- LHS of composition is surjective if the composition is surjective.
  [∘]-surjective-elim : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Surjective{ℓₒ}{ℓₒ}(f ∘ g) ⦄ → Surjective{ℓₒ}{ℓₒ}(f)
  Surjective.proof([∘]-surjective-elim {f = f}{g = g}) {y} with (surjective(f ∘ g) {y})
  ... | [∃]-intro (x) ⦃ [≡]-intro ⦄ = [∃]-intro (g(x)) ⦃ [≡]-intro ⦄

  -- Every injective function has a left inverse with respect to function composition.
  {-[∘]-inverseₗ-value : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Injective(f) ⦄ → ∃(g ↦ ∀{x} → ((g ∘ f)(x) ≡ id(x)))
  [∘]-inverseₗ-value {a}{b} {f} ⦃ f-injective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : b → a
    f⁻¹(y) = 

    f⁻¹-proof : ∀{y} → ((f ∘ f⁻¹)(y) ≡ id(y))
    f⁻¹-proof{y} = 
  -}

  instance
    [∘]-bijective : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Bijective{ℓₒ}{ℓₒ}(f) ⦄ → ⦃ _ : Bijective{ℓₒ}{ℓₒ}(g) ⦄ → Bijective{ℓₒ}{ℓₒ}(f ∘ g)
    [∘]-bijective {f = f}{g} ⦃ bij-f ⦄ ⦃ bij-g ⦄ =
      injective-surjective-to-bijective(f ∘ g)
        ⦃ [∘]-injective
          ⦃ bijective-to-injective(f) ⦃ bij-f ⦄ ⦄
          ⦃ bijective-to-injective(g) ⦃ bij-g ⦄ ⦄
        ⦄
        ⦃ [∘]-surjective
          ⦃ bijective-to-surjective(f) ⦃ bij-f ⦄ ⦄
          ⦃ bijective-to-surjective(g) ⦃ bij-g ⦄ ⦄
        ⦄

  instance
    [∘]-function : ∀{a b c : Type{ℓₒ}}{f : b → c}{g : a → b} → ⦃ _ : Function(f) ⦄ → ⦃ _ : Function(g) ⦄ → Function(f ∘ g)
    Function.proof([∘]-function {f = f}{g = g} ⦃ func-f ⦄ ⦃ func-g ⦄ ) {x₁}{x₂} = (function-proof(f) ⦃ func-f ⦄ {g(x₁)} {g(x₂)}) ∘ (function-proof(g) ⦃ func-g ⦄ {x₁} {x₂})

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv(B) ⦄ where
  private
    _⊜AB_ = _⊜_ {A = A}{B} ⦃ eqB ⦄
    _⊜BA_ = _⊜_ {A = B}{A} ⦃ eqA ⦄
    _⊜AA_ = _⊜_ {A = A}{A} ⦃ eqA ⦄
    _⊜BB_ = _⊜_ {A = B}{B} ⦃ eqB ⦄

  -- Every surjective function has a right inverse with respect to function composition.
  -- Note: Equivalent to axiom of choice from set theory when formulated in classical logic.
  [∘]-inverseᵣ-value : ∀{f : A → B} → ⦃ _ : Surjective(f) ⦄ → ∃{Obj = B → A}(g ↦ f ∘ g ⊜BB id)
  [∘]-inverseᵣ-value {f} ⦃ f-surjective ⦄ = [∃]-intro (f⁻¹) ⦃ (\{x} → f⁻¹-proof{x}) ⦄ where
    f⁻¹ : B → A
    f⁻¹(y) = [∃]-witness(surjective(f) {y})

    f⁻¹-proof : (f ∘ f⁻¹ ⊜ id)
    f⁻¹-proof{y} = [∃]-proof(surjective(f) {y})

  -- TODO: Are these really provable?
  -- postulate [∘]-inverseₗ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ g ∘ f ≡ id)
  -- postulate [∘]-inverseᵣ : ∀{a b : Type{ℓₒ}}{f : a → b} → ⦃ _ : Bijective(f) ⦄ → ∃(g ↦ f ∘ g ≡ id)

  -- TODO: 
  -- inv-fnₗ : ∀{a b} → (f : a → b) → ⦃ _ : Bijective(f) ⦄ → (b → a)
  -- inv-fnₗ (f) = [∃]-witness([∘]-inverseₗ{_}{_}{f})

  inv-fnᵣ : (f : A → B) → ⦃ _ : Surjective(f) ⦄ → (B → A)
  inv-fnᵣ(f) = [∃]-witness([∘]-inverseᵣ-value{f = f})

  inv-fn : (f : A → B) → ⦃ _ : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (B → A)
  inv-fn(f) = inv-fnᵣ(f) ⦃ bijective-to-surjective(f) ⦄

  inv-fnᵣ-inverseᵣ : ∀{f} → ⦃ _ : Surjective(f) ⦄ → (f ∘ inv-fnᵣ(f) ⊜ id)
  inv-fnᵣ-inverseᵣ{f} = [∃]-proof([∘]-inverseᵣ-value{f = f})

  inv-fn-inverseᵣ : ∀{f} → ⦃ _ : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (f ∘ inv-fn(f) ⊜ id)
  inv-fn-inverseᵣ{f} = inv-fnᵣ-inverseᵣ{f} ⦃ bijective-to-surjective(f) ⦄

  inv-fn-inverseₗ : ∀{f} → ⦃ _ : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ → (inv-fn(f) ∘ f ⊜AA id)
  inv-fn-inverseₗ{f} = [∃!]-existence-eq-any (bijective(f)) (reflexivity(_≡ₛ_))

  module _ {f : A → B} ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ where
    inv-surjective : Surjective ⦃ eqA ⦄ (inv-fn f)
    Surjective.proof(inv-surjective) {x} = [∃]-intro(f(x)) ⦃ inv-fn-inverseₗ {f} ⦃ bij ⦄ ⦄

  module _ {f : A → B} ⦃ func : Function ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ ⦃ bij : Bijective ⦃ eqA ⦄ ⦃ eqB ⦄ (f) ⦄ where
    inv-function : Function ⦃ eqB ⦄ ⦃ eqA ⦄ (inv-fn f)
    Function.proof(inv-function) {x₁}{x₂} (x₁≡x₂) =
      injective(f) ⦃ bijective-to-injective(f) ⦄ {inv-fn f(x₁)} {inv-fn f(x₂)}
        (
          inv-fn-inverseᵣ{f}{x₁}
          🝖 x₁≡x₂
          🝖 symmetry(_≡ₛ_) (inv-fn-inverseᵣ{f} {x₂})
        )

    inv-injective : Injective(inv-fn f)
    Injective.proof(inv-injective) {x₁}{x₂} (invfx₁≡invfx₂) =
      symmetry(_≡ₛ_) (inv-fn-inverseᵣ{f}{x₁})
      🝖 function-proof(f) ⦃ func ⦄ {inv-fn f(x₁)} {inv-fn f(x₂)} (invfx₁≡invfx₂)
      🝖 inv-fn-inverseᵣ{f}{x₂}

    inv-bijective : Bijective(inv-fn f)
    inv-bijective = injective-surjective-to-bijective(inv-fn f) ⦃ inv-injective ⦄ ⦃ inv-surjective ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  swap-involution : ∀{f : X → Y → Z} → (swap(swap(f)) ≡ f)
  swap-involution = [≡]-intro

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
