module Function.Proofs where

import      Lvl
open import Logic
open import Logic.Classical
open import Logic.Computability
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Inverseᵣ
open import Function.Names using (_⊜_)
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Structure.Setoid.Uniqueness
import      Structure.Relator.Function as Relator
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function renaming (congruence₁ to [≡ₛ]-with)
open import Structure.Operator
open import Syntax.Transitivity
open import Type
open import Type.Empty

module _ {ℓₗ ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}}{B : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}} ⦃ equiv-B : Equiv(B) ⦄ (φ : A → B → Stmt{ℓₗ}) ⦃ totality : Relator.Total(φ)⦄ ⦃ func : Relator.Function(φ)⦄ ⦃ _ : ∀{x} → UnaryRelator(φ(x)) ⦄ where
  -- There is a function for a binary relation that is total and function-like.
  relation-function-existence : ∃(f ↦ ∀{x}{y} → (f(x) ≡ₛ y) ↔ φ(x)(y))
  relation-function-existence = [∃]-intro(f) ⦃ \{x y} → proof{x}{y} ⦄ where
    -- The function
    f : A → B
    f(x) = [∃]-witness(Relator.total(φ){x})

    -- Proof that the function returns the value that the binary relation defines the element from Y that an element from X is associated with.
    proof : ∀{x}{y} → (f(x) ≡ₛ y) ↔ φ(x)(y)
    proof{x}{y} = [↔]-intro l r where
      r : (f(x) ≡ₛ y) → φ(x)(y)
      r(fxy) = substitute₁(φ(x)) fxy ([∃]-proof(Relator.total(φ){x}))

      l : (f(x) ≡ₛ y) ← φ(x)(y)
      l(φxy) = [∃!]-existence-eq-any(Relator.totalFunction(φ)) φxy

  -- Constructing a total function from a a binary operation with conditions.
  relation-function : A → B
  relation-function = [∃]-witness(relation-function-existence)

module _ {ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ {f : A → B} where
  -- A function is total
  -- ∀{x} → ∃(y ↦ f(x) ≡ y)
  Function-totality : Relator.Total(x ↦ y ↦ f(x) ≡ₛ y)
  Relator.Total.proof(Function-totality) {x} = [∃]-intro(f(x)) ⦃ reflexivity(_≡ₛ_) ⦄

module _ {ℓₗ ℓₒ₁ ℓₒ₂} {X : Type{ℓₒ₁}} {Y : X → Type{ℓₒ₂}} {φ : (x : X) → Y(x) → Stmt{ℓₗ}} where
  -- Every binary predicate that have its first argument defined for all values
  -- have at least one choice function that can determine the second argument from the first.
  -- Proposition: ∀(X: Type)∀(Y: Type)∀(φ: X → Y → Stmt). (∀(x: X)∃(y: Y). φ(x)(y)) → (∃(choice: X → Y)∀(x: X). φ(x)(choice(x)))
  --   ∀(x: X)∃(y: Y). φ(x)(y) means that the predicate φ holds for every x and some y (which may depend on x). In other words: it associates every element in X with a subset of Y, a function (X → ℘(Y)).
  --   ∃(choice: X → Y)∀(x: X). φ(x)(choice(x)) means that there is a function that picks out a particular y.
  -- Note: This proposition can be recognised as one equivalent variant of "Axiom of Choice" from set theory when formulated in classical logic.
  dependent-function-predicate-choice : (∀{x : X} → ∃{Obj = Y(x)}(y ↦ φ(x)(y))) → ∃{Obj = (x : X) → Y(x)}(choice ↦ ∀{x : X} → φ(x)(choice(x)))
  dependent-function-predicate-choice(function) = [∃]-intro(x ↦ [∃]-witness(function{x})) ⦃ \{x} → [∃]-proof(function{x}) ⦄

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

module _ {ℓₒ}{T : Type{ℓₒ}} ⦃ eq : Equiv(T) ⦄ where
  instance
    -- Identity function is a function.
    id-function : Function(id)
    Function.congruence(id-function) = id

  instance
    -- Identity function is injective.
    id-injective : Injective(id)
    Injective.proof(id-injective) = id

  instance
    -- Identity function is surjective.
    id-surjective : Surjective(id)
    Surjective.proof(id-surjective) {y} = [∃]-intro (y) ⦃ reflexivity(_≡ₛ_) ⦄

  instance
    -- Identity function is bijective.
    id-bijective : Bijective(id)
    id-bijective = injective-surjective-to-bijective(id)

module _ {ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ eq-a : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ eq-b : Equiv(B) ⦄ where
  instance
    -- Constant functions are functions.
    const-function : ∀{c : B} → Function {A = A}{B = B} (const(c))
    Function.congruence(const-function) _ = reflexivity(_≡ₛ_)

module _ {ℓₒ₁ ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ eq-a : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ eq-b : Equiv(B) ⦄ where
  open import Function.Equals
  open import Function.Equals.Proofs

  -- The constant function is extensionally a function.
  instance
    const-function-function : ∀{c : B} → Function {A = B}{B = A → B} const
    Function.congruence const-function-function = [⊜]-abstract

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄} {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}}{c : Type{ℓₒ₃}}{d : Type{ℓₒ₄}} ⦃ _ : Equiv(a → d) ⦄ where
  -- Function composition is associative.
  [∘]-associativity : ∀{f : c → d}{g : b → c}{h : a → b} → ((f ∘ (g ∘ h)) ≡ₛ ((f ∘ g) ∘ h))
  [∘]-associativity = reflexivity(_≡ₛ_)

module _ {ℓₒ₁ ℓₒ₂} {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}} ⦃ _ : Equiv(a → b) ⦄ {f : a → b} where
  -- Function composition has left identity element.
  [∘]-identityₗ : (id ∘ f ≡ₛ f)
  [∘]-identityₗ = reflexivity(_≡ₛ_)

  -- Function composition has right identity element.
  [∘]-identityᵣ : (f ∘ id ≡ₛ f)
  [∘]-identityᵣ = reflexivity(_≡ₛ_)

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {a : Type{ℓₒ₁}} ⦃ _ : Equiv(a) ⦄ {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv(c) ⦄ where
  -- The composition of injective functions is injective.
  -- Source: https://math.stackexchange.com/questions/2049511/is-the-composition-of-two-injective-functions-injective/2049521
  -- Alternative proof: [∘]-associativity {f⁻¹}{g⁻¹}{g}{f} becomes id by inverseₗ-value injective equivalence
  [∘]-injective : ∀{f : b → c}{g : a → b} → ⦃ _ : Injective(f) ⦄ → ⦃ _ : Injective(g) ⦄ → Injective(f ∘ g)
  Injective.proof([∘]-injective {f = f}{g = g} ⦃ inj-f ⦄ ⦃ inj-g ⦄ ) {x₁}{x₂} = (injective(g) ⦃ inj-g ⦄ {x₁} {x₂}) ∘ (injective(f) ⦃ inj-f ⦄ {g(x₁)} {g(x₂)})

  -- RHS of composition is injective if the composition is injective.
  [∘]-injective-elim : ∀{f : b → c} → ⦃ _ : Function(f) ⦄ → ∀{g : a → b} → ⦃ _ : Injective(f ∘ g) ⦄ → Injective(g)
  Injective.proof([∘]-injective-elim {f = f}{g = g} ⦃ inj-fg ⦄) {x₁}{x₂} (gx₁gx₂) = injective(f ∘ g) ⦃ inj-fg ⦄ {x₁} {x₂} ([≡ₛ]-with(f) (gx₁gx₂))

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {a : Type{ℓₒ₁}} {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv(c) ⦄ where
  -- The composition of surjective functions is surjective.
  [∘]-surjective : ∀{f : b → c} → ⦃ _ : Function(f) ⦄ → ∀{g : a → b} → ⦃ _ : Surjective(f) ⦄ → ⦃ _ : Surjective(g) ⦄ → Surjective(f ∘ g)
  Surjective.proof([∘]-surjective {f = f}{g = g}) {y}
    with (surjective(f) {y})
  ... | [∃]-intro (a) ⦃ fa≡y ⦄
    with (surjective(g) {a})
  ... | [∃]-intro (x) ⦃ gx≡a ⦄
    = [∃]-intro (x) ⦃ [≡ₛ]-with(f) (gx≡a) 🝖 fa≡y ⦄

  -- LHS of composition is surjective if the composition is surjective.
  [∘]-surjective-elim : ∀{f : b → c}{g : a → b} → ⦃ _ : Surjective(f ∘ g) ⦄ → Surjective(f)
  Surjective.proof([∘]-surjective-elim {f = f}{g = g}) {y} with (surjective(f ∘ g) {y})
  ... | [∃]-intro (x) ⦃ fgx≡y ⦄ = [∃]-intro (g(x)) ⦃ fgx≡y ⦄

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
  [∘]-function : ∀{f : b → c}{g : a → b} → ⦃ func-f : Function(f) ⦄ → ⦃ func-g : Function(g) ⦄ → Function(f ∘ g)
  Function.congruence([∘]-function {f = f}{g = g} ⦃ func-f ⦄ ⦃ func-g ⦄ ) {x₁}{x₂} = ([≡ₛ]-with(f) ⦃ func-f ⦄ {g(x₁)} {g(x₂)}) ∘ ([≡ₛ]-with(g) ⦃ func-g ⦄ {x₁} {x₂})

module _ {ℓₒ₁ ℓₒ₂} {a : Type{ℓₒ₁}} ⦃ _ : Equiv(a) ⦄ {b : Type{ℓₒ₂}} ⦃ _ : Equiv(b) ⦄ where
  open import Function.Equals
  open import Structure.Function.Domain.Proofs

  [∘]-inverse-to-injective : ∀{f : a → b} → ∃(g ↦ Function(g) ∧ (g ∘ f ≡ₛ id)) → Injective(f)
  [∘]-inverse-to-injective {f} ([∃]-intro g ⦃ [∧]-intro func-g gfid ⦄) = [∘]-injective-elim {f = g} ⦃ func-g ⦄ {g = f} ⦃ substitute₁(Injective) (symmetry(_≡ₛ_) gfid) id-injective ⦄

  [∘]-inverse-to-surjective : ∀{f : a → b} → ∃(g ↦ Function(g) ∧ (f ∘ g ≡ₛ id)) → Surjective(f)
  [∘]-inverse-to-surjective {f} ([∃]-intro g ⦃ [∧]-intro func-g fgid ⦄) = [∘]-surjective-elim {f = f}{g = g} ⦃ substitute₁(Surjective) (symmetry(_≡ₛ_) fgid) id-surjective ⦄

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  swap-involution : ⦃ _ : Equiv(X → Y → Z) ⦄ → ∀{f : X → Y → Z} → (swap(swap(f)) ≡ₛ f)
  swap-involution = reflexivity(_≡ₛ_)

  swap-involution-fn : ⦃ _ : Equiv((X → Y → Z) → (X → Y → Z)) ⦄ → (swap ∘ swap ≡ₛ id {T = X → Y → Z})
  swap-involution-fn = reflexivity(_≡ₛ_)

  swap-binaryOperator : ⦃ _ : Equiv(X) ⦄ ⦃ _ : Equiv(Y) ⦄ ⦃ _ : Equiv(Z) ⦄ → ∀{_▫_ : X → Y → Z} → ⦃ _ : BinaryOperator(_▫_) ⦄ → BinaryOperator(swap(_▫_))
  BinaryOperator.congruence (swap-binaryOperator {_▫_ = _▫_} ⦃ intro p ⦄) x₁y₁ x₂y₂ = p x₂y₂ x₁y₁

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  s-combinator-const-id : ⦃ _ : Equiv(X → X) ⦄ → (_∘ₛ_ {X = X}{Y = Y → X}{Z = X} const const ≡ₛ id)
  s-combinator-const-id = reflexivity(_≡ₛ_)

module _ {ℓ₁ ℓ₂ ℓ₃} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} ⦃ equiv-z : Equiv(Z) ⦄ where
  s-combinator-const-eq : ∀{f}{a}{b} → (_∘ₛ_{X = X}{Y = Y}{Z = Z} f (const b) a ≡ₛ f a b)
  s-combinator-const-eq = reflexivity(_≡ₛ_)

{- TODO: Maybe this is unprovable because types. https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog https://plato.stanford.edu/entries/axiom-choice/choice-and-type-theory.html https://en.wikipedia.org/wiki/Diaconescu%27s_theorem
module _ {fn-ext : FunctionExtensionality} where
  open import Function.Names
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

module _ {ℓₒ₁ ℓₒ₂ ℓₒ₃} {X : Type{ℓₒ₁}} ⦃ eq-x : Equiv(X) ⦄ {Y : Type{ℓₒ₂}} ⦃ eq-y : Equiv(Y) ⦄ {Z : Type{ℓₒ₃}} ⦃ eq-z : Equiv(Z) ⦄ where
  open import Function.Equals
  open import Function.Equals.Proofs

  s-combinator-injective : Injective(_∘ₛ_ {X = X}{Y = Y}{Z = Z})
  _⊜_.proof (Injective.proof s-combinator-injective {f} {g} sxsy) {x} = Function.Equals.intro(\{a} → [⊜]-apply([⊜]-apply sxsy {const(a)}){x}) -- TODO: Left inverse (S⁻¹ ∘ S = id) is probably (S⁻¹ f a b = f (const b) a)
