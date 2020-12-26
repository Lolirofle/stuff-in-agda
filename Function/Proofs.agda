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
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function
open import Structure.Operator
open import Syntax.Transitivity
open import Type
open import Type.Properties.Empty

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₒ₅ ℓₒ₆ ℓₒ₇ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ ℓₑ₇ : Lvl.Level

module _ {T : Type{ℓₒ}} ⦃ eq : Equiv{ℓₑ}(T) ⦄ where
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

  instance
    id-idempotent : Idempotent(id)
    id-idempotent = intro(reflexivity _)

  instance
    id-involution : Involution(id)
    id-involution = intro(reflexivity _)

  instance
    id-inverseₗ : Inverseₗ(id)(id)
    id-inverseₗ = intro(reflexivity _)

  instance
    id-inverseᵣ : Inverseᵣ(id)(id)
    id-inverseᵣ = intro(reflexivity _)

  instance
    id-inverse : Inverse(id)(id)
    id-inverse = [∧]-intro id-inverseₗ id-inverseᵣ

module _ {A : Type{ℓₒ₁}} ⦃ eq-a : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ eq-b : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    -- Constant functions are functions.
    const-function : ∀{c : B} → Function {A = A}{B = B} (const(c))
    Function.congruence(const-function) _ = reflexivity(_≡ₛ_)

  instance
    -- Constant functions are constant.
    const-constant : ∀{c : B} → Constant {A = A}{B = B} (const(c))
    Constant.proof const-constant = reflexivity(_≡ₛ_)

module _ {A : Type{ℓₒ₁}} ⦃ eq-a : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ eq-b : Equiv{ℓₑ₂}(B) ⦄ where
  open import Function.Equals
  open import Function.Equals.Proofs

  -- The constant function is extensionally a function.
  instance
    const-function-function : ∀{c : B} → Function {A = B}{B = A → B} const
    Function.congruence const-function-function = [⊜]-abstract

module _ {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}}{c : Type{ℓₒ₃}}{d : Type{ℓₒ₄}} ⦃ _ : Equiv{ℓₑ}(a → d) ⦄ where
  -- Function composition is associative.
  [∘]-associativity : ∀{f : c → d}{g : b → c}{h : a → b} → ((f ∘ (g ∘ h)) ≡ₛ ((f ∘ g) ∘ h))
  [∘]-associativity = reflexivity(_≡ₛ_)

module _ {a : Type{ℓₒ₁}}{b : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ}(a → b) ⦄ {f : a → b} where
  -- Function composition has left identity element.
  [∘]-identityₗ : (id ∘ f ≡ₛ f)
  [∘]-identityₗ = reflexivity(_≡ₛ_)

  -- Function composition has right identity element.
  [∘]-identityᵣ : (f ∘ id ≡ₛ f)
  [∘]-identityᵣ = reflexivity(_≡ₛ_)

module _ {a : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₑ₁}(a) ⦄ {b : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ₂}(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv{ℓₑ₃}(c) ⦄ where
  -- The composition of injective functions is injective.
  -- Source: https://math.stackexchange.com/questions/2049511/is-the-composition-of-two-injective-functions-injective/2049521
  -- Alternative proof: [∘]-associativity {f⁻¹}{g⁻¹}{g}{f} becomes id by inverseₗ-value injective equivalence
  [∘]-injective : ∀{f : b → c}{g : a → b} → ⦃ inj-f : Injective(f) ⦄ → ⦃ inj-g : Injective(g) ⦄ → Injective(f ∘ g)
  Injective.proof([∘]-injective {f = f}{g = g} ⦃ inj-f ⦄ ⦃ inj-g ⦄ ) {x₁}{x₂} = (injective(g) ⦃ inj-g ⦄ {x₁} {x₂}) ∘ (injective(f) ⦃ inj-f ⦄ {g(x₁)} {g(x₂)})

  -- RHS of composition is injective if the composition is injective.
  [∘]-injective-elim : ∀{f : b → c} → ⦃ func-f : Function(f) ⦄ → ∀{g : a → b} → ⦃ inj-fg : Injective(f ∘ g) ⦄ → Injective(g)
  Injective.proof([∘]-injective-elim {f = f}{g = g} ⦃ inj-fg ⦄) {x₁}{x₂} (gx₁gx₂) = injective(f ∘ g) ⦃ inj-fg ⦄ {x₁} {x₂} (congruence₁(f) (gx₁gx₂))

module _ {a : Type{ℓₒ₁}} {b : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ₂}(b) ⦄ {c : Type{ℓₒ₃}} ⦃ _ : Equiv{ℓₑ₃}(c) ⦄ where
  -- The composition of surjective functions is surjective.
  [∘]-surjective : ∀{f : b → c} → ⦃ func-f : Function(f) ⦄ → ∀{g : a → b} → ⦃ surj-f : Surjective(f) ⦄ → ⦃ surj-g : Surjective(g) ⦄ → Surjective(f ∘ g)
  Surjective.proof([∘]-surjective {f = f}{g = g}) {y}
    with [∃]-intro (a) ⦃ fa≡y ⦄ ← surjective(f) {y}
    with [∃]-intro (x) ⦃ gx≡a ⦄ ← surjective(g) {a}
    = [∃]-intro (x) ⦃ congruence₁(f) gx≡a 🝖 fa≡y ⦄

  -- LHS of composition is surjective if the composition is surjective.
  [∘]-surjective-elim : ∀{f : b → c}{g : a → b} → ⦃ _ : Surjective(f ∘ g) ⦄ → Surjective(f)
  Surjective.proof([∘]-surjective-elim {f = f}{g = g}) {y} with (surjective(f ∘ g) {y})
  ... | [∃]-intro (x) ⦃ fgx≡y ⦄ = [∃]-intro (g(x)) ⦃ fgx≡y ⦄

module _
  {a : Type{ℓₒ₁}} ⦃ equiv-a : Equiv{ℓₑ₁}(a) ⦄
  {b : Type{ℓₒ₂}} ⦃ equiv-b : Equiv{ℓₑ₂}(b) ⦄
  {c : Type{ℓₒ₃}} ⦃ equiv-c : Equiv{ℓₑ₃}(c) ⦄
  where

  -- Bijective functions are closed under function composition.
  -- The composition of bijective functions is bijective.
  [∘]-bijective : ∀{f : b → c} → ⦃ func-f : Function(f) ⦄ → ∀{g : a → b} → ⦃ bij-f : Bijective(f) ⦄ → ⦃ bij-g : Bijective(g) ⦄ → Bijective(f ∘ g)
  [∘]-bijective {f = f} {g = g} =
    injective-surjective-to-bijective(f ∘ g)
      ⦃ [∘]-injective
        ⦃ inj-f = bijective-to-injective(f) ⦄
        ⦃ inj-g = bijective-to-injective(g) ⦄
      ⦄
      ⦃ [∘]-surjective
        ⦃ surj-f = bijective-to-surjective(f) ⦄
        ⦃ surj-g = bijective-to-surjective(g) ⦄
      ⦄

  -- The composition of functions is a function.
  [∘]-function : ∀{f : b → c}{g : a → b} → ⦃ func-f : Function(f) ⦄ → ⦃ func-g : Function(g) ⦄ → Function(f ∘ g)
  Function.congruence([∘]-function {f = f}{g = g}) = congruence₁(f) ∘ congruence₁(g)

module _
  {a₁ : Type{ℓₒ₁}} ⦃ equiv-a₁ : Equiv{ℓₑ₁}(a₁) ⦄
  {b₁ : Type{ℓₒ₂}} ⦃ equiv-b₁ : Equiv{ℓₑ₂}(b₁) ⦄
  {a₂ : Type{ℓₒ₃}} ⦃ equiv-a₂ : Equiv{ℓₑ₃}(a₂) ⦄
  {b₂ : Type{ℓₒ₄}} ⦃ equiv-b₂ : Equiv{ℓₑ₄}(b₂) ⦄
  {c  : Type{ℓₒ₅}} ⦃ equiv-c  : Equiv{ℓₑ₅}(c) ⦄
  {f : a₂ → b₂ → c}  ⦃ func-f : BinaryOperator(f) ⦄
  {g : a₁ → b₁ → a₂} ⦃ func-g : BinaryOperator(g) ⦄
  {h : a₁ → b₁ → b₂} ⦃ func-h : BinaryOperator(h) ⦄
  where

  [∘]-binaryOperator : BinaryOperator(x ↦ y ↦ f(g x y)(h x y))
  BinaryOperator.congruence [∘]-binaryOperator xy1 xy2 = congruence₂(f) (congruence₂(g) xy1 xy2) (congruence₂(h) xy1 xy2)

module _
  {a : Type{ℓₒ₁}} ⦃ equiv-a : Equiv{ℓₑ₁}(a) ⦄
  {b : Type{ℓₒ₂}} ⦃ equiv-b : Equiv{ℓₑ₂}(b) ⦄
  {f : a → a → b}  ⦃ func-f : BinaryOperator(f) ⦄
  where

  [$₂]-function : Function(f $₂_)
  Function.congruence [$₂]-function = congruence₂(f) $₂_

module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} where
  swap-involution : ⦃ _ : Equiv{ℓₑ}(X → Y → Z) ⦄ → ∀{f : X → Y → Z} → (swap(swap(f)) ≡ₛ f)
  swap-involution = reflexivity(_≡ₛ_)

  swap-involution-fn : ⦃ _ : Equiv{ℓₑ}((X → Y → Z) → (X → Y → Z)) ⦄ → (swap ∘ swap ≡ₛ id {T = X → Y → Z})
  swap-involution-fn = reflexivity(_≡ₛ_)

  swap-binaryOperator : ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ ⦃ _ : Equiv{ℓₑ₃}(Z) ⦄ → ∀{_▫_ : X → Y → Z} → ⦃ _ : BinaryOperator(_▫_) ⦄ → BinaryOperator(swap(_▫_))
  BinaryOperator.congruence (swap-binaryOperator {_▫_ = _▫_} ⦃ intro p ⦄) x₁y₁ x₂y₂ = p x₂y₂ x₁y₁

module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  s-combinator-const-id : ⦃ _ : Equiv{ℓₑ}(X → X) ⦄ → (_∘ₛ_ {X = X}{Y = Y → X}{Z = X} const const ≡ₛ id)
  s-combinator-const-id = reflexivity(_≡ₛ_)

module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} {Z : Type{ℓ₃}} ⦃ equiv-z : Equiv{ℓₑ₃}(Z) ⦄ where
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

module _ {X : Type{ℓₒ₁}} ⦃ eq-x : Equiv{ℓₑ₁}(X) ⦄ {Y : Type{ℓₒ₂}} ⦃ eq-y : Equiv{ℓₑ₂}(Y) ⦄ {Z : Type{ℓₒ₃}} ⦃ eq-z : Equiv{ℓₑ₃}(Z) ⦄ where
  open import Function.Equals
  open import Function.Equals.Proofs

  s-combinator-injective : Injective(_∘ₛ_ {X = X}{Y = Y}{Z = Z})
  _⊜_.proof (Injective.proof s-combinator-injective {f} {g} sxsy) {x} = Function.Equals.intro(\{a} → [⊜]-apply([⊜]-apply sxsy {const(a)}){x})

  s-combinator-inverseₗ : Inverseₗ(_∘ₛ_ {X = X}{Y = Y}{Z = Z})(f ↦ a ↦ b ↦ f (const b) a)
  _⊜_.proof (Inverseᵣ.proof s-combinator-inverseₗ) = reflexivity(_≡ₛ_)

module _ {A : Type{ℓ}} ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄ where
  classical-constant-endofunction-existence : ⦃ classical : Classical(A) ⦄ → ∃{Obj = A → A}(Constant)
  classical-constant-endofunction-existence with excluded-middle(A)
  ... | [∨]-introₗ a  = [∃]-intro (const a)
  ... | [∨]-introᵣ na = [∃]-intro id ⦃ intro(\{a} → [⊥]-elim(na a)) ⦄

module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open import Logic.Propositional.Theorems
  open import Structure.Operator.Properties

  proj₂ₗ-associativity : Associativity{T = T}(proj₂ₗ)
  proj₂ₗ-associativity = intro(reflexivity(_))

  proj₂ᵣ-associativity : Associativity{T = T}(proj₂ᵣ)
  proj₂ᵣ-associativity = intro(reflexivity(_))

  proj₂ₗ-identityₗ : ∀{id : T} → Identityₗ(proj₂ₗ)(id) ↔ (∀{x} → (Equiv._≡_ equiv id x))
  proj₂ₗ-identityₗ = [↔]-intro intro Identityₗ.proof

  proj₂ₗ-identityᵣ : ∀{id : T} → Identityᵣ(proj₂ₗ)(id)
  proj₂ₗ-identityᵣ = intro(reflexivity(_))

  proj₂ₗ-identity : ∀{id : T} → Identity(proj₂ₗ)(id) ↔ (∀{x} → (Equiv._≡_ equiv id x))
  proj₂ₗ-identity =
    [↔]-transitivity
      ([↔]-intro (l ↦ intro ⦃ left = l ⦄ ⦃ right = proj₂ₗ-identityᵣ ⦄) Identity.left)
      proj₂ₗ-identityₗ

  proj₂ᵣ-identityₗ : ∀{id : T} → Identityₗ(proj₂ᵣ)(id)
  proj₂ᵣ-identityₗ = intro(reflexivity(_))

  proj₂ᵣ-identityᵣ : ∀{id : T} → Identityᵣ(proj₂ᵣ)(id) ↔ (∀{x} → (Equiv._≡_ equiv id x))
  proj₂ᵣ-identityᵣ = [↔]-intro intro Identityᵣ.proof

  proj₂ᵣ-identity : ∀{id : T} → Identity(proj₂ᵣ)(id) ↔ (∀{x} → (Equiv._≡_ equiv id x))
  proj₂ᵣ-identity =
    [↔]-transitivity
      ([↔]-intro (r ↦ intro ⦃ left = proj₂ᵣ-identityₗ ⦄ ⦃ right = r ⦄) Identity.right)
      proj₂ᵣ-identityᵣ
