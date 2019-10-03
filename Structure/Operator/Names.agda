module Structure.Operator.Names where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Syntax.Function
open import Functional.Names
open import Type

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ where
  -- Definition of commutativity
  Commutativity : (T₁ → T₁ → T₂) → Stmt
  Commutativity (_▫_) = ∀{x y : T₁} → (x ▫ y) ≡ (y ▫ x)

  -- Definition of an left identity element
  Identityₗ : (T₁ → T₂ → T₂) → T₁ → Stmt
  Identityₗ (_▫_) id = ∀{x : T₂} → (id ▫ x) ≡ x

  -- Definition of a right absorber element
  -- Also called "right neutral element" or "right annihilator"
  Absorberᵣ : (T₁ → T₂ → T₂) → T₂ → Stmt
  Absorberᵣ (_▫_) null = ∀{x : T₁} → (x ▫ null) ≡ null

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Type{ℓ₂}} where
  -- Definition of an right identity element
  Identityᵣ : (T₁ → T₂ → T₁) → T₂ → Stmt
  Identityᵣ (_▫_) id = ∀{x : T₁} → (x ▫ id) ≡ x

  -- Definition of a left absorber element
  -- Also called "left neutral element" or "left annihilator"
  Absorberₗ : (T₁ → T₂ → T₁) → T₁ → Stmt
  Absorberₗ (_▫_) null = ∀{x : T₂} → (null ▫ x) ≡ null

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
  -- Definition of an identity element
  Identity : (T → T → T) → T → Stmt
  Identity (_▫_) id = (Identityₗ (_▫_) id) ∧ (Identityᵣ (_▫_) id)

  -- Definition of idempotence
  Idempotence : (T → T → T) → Stmt
  Idempotence (_▫_) = ∀{x : T} → (x ▫ x ≡ x)

module _ {ℓ₁ ℓ₂ ℓ₃} {T₊ : Type{ℓ₁}} {T₋ : Type{ℓ₂}} {Tᵣ : Type{ℓ₃}} ⦃ _ : Equiv(Tᵣ) ⦄ where
  -- Definition of a left invertible element
  Invertibleₗ : (T₋ → T₊ → Tᵣ) → Tᵣ → T₊ → Stmt
  Invertibleₗ (_▫_) id x = ∃(inv ↦ (inv ▫ x) ≡ id)

  -- Definition of a right invertible element
  Invertibleᵣ : (T₋ → T₊ → Tᵣ) → Tᵣ → T₋ → Stmt
  Invertibleᵣ (_▫_) id x = ∃(inv ↦ (x ▫ inv) ≡ id)

  -- Definition of a left inverse function
  InverseFunctionₗ : (T₋ → T₊ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
  InverseFunctionₗ (_▫_) id inv = ∀{x : T₊} → ((inv x) ▫ x) ≡ id

  -- Definition of a right inverse function
  InverseFunctionᵣ : (T₊ → T₋ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
  InverseFunctionᵣ (_▫_) id inv = ∀{x : T₊} → (x ▫ (inv x)) ≡ id

module _ {ℓ₁ ℓ₂} {T : Type{ℓ₁}} {Tᵣ : Type{ℓ₂}} ⦃ _ : Equiv(Tᵣ) ⦄ where
  -- Definition of an invertible element
  Invertible : (T → T → Tᵣ) → Tᵣ → T → Stmt
  Invertible (_▫_) id x = ∃(inv ↦ ((inv ▫ x) ≡ id) ∧ ((x ▫ inv) ≡ id))

  -- Definition of a function which returns the inverse element of the other side of the operation
  InverseFunction : (T → T → Tᵣ) → Tᵣ → (T → T) → Stmt
  InverseFunction (_▫_) id inv = (InverseFunctionₗ (_▫_) id inv) ∧ (InverseFunctionᵣ (_▫_) id inv)

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₃) ⦄ where
  -- Definition of a left inverse operator
  InverseOperatorₗ : (T₁ → T₂ → T₃) → (T₁ → T₃ → T₂) → Stmt
  InverseOperatorₗ (_▫₁_) (_▫₂_) = ∀{x}{y}{z} → ((x ▫₁ y) ≡ z) ↔ (y ≡ (x ▫₂ z)) -- TODO: Is this implied by InverseFunction?

  -- Definition of right cancellation of a specific object
  -- ∀{a b : T₂} → ((x ▫ a) ≡ (x ▫ b)) → (a ≡ b)
  CancellationOnₗ : (T₁ → T₂ → T₃) → T₁ → Stmt
  CancellationOnₗ (_▫_) (x) = Injective(x ▫_)

  -- Definition of left cancellation (Injectivity for the right param)
  -- ∀{x : T₁}{a b : T₂} → ((x ▫ a) ≡ (x ▫ b)) → (a ≡ b)
  Cancellationₗ : (T₁ → T₂ → T₃) → Stmt
  Cancellationₗ (_▫_) = (∀{x : T₁} → CancellationOnₗ(_▫_)(x))

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₃) ⦄ where
  -- Definition of a right inverse operator
  InverseOperatorᵣ : (T₁ → T₂ → T₃) → (T₃ → T₂ → T₁) → Stmt
  InverseOperatorᵣ (_▫₁_) (_▫₂_) = ∀{x}{y}{z} → ((x ▫₁ y) ≡ z) ↔ (x ≡ (z ▫₂ y))

  -- Definition of right cancellation of a specific object
  -- ∀{a b : T₁} → ((a ▫ x) ≡ (b ▫ x)) → (a ≡ b)
  CancellationOnᵣ : (T₁ → T₂ → T₃) → T₂ → Stmt
  CancellationOnᵣ (_▫_) (x) = Injective(_▫ x)

  -- Definition of right cancellation (Injectivity for the left param)
  -- ∀{x : T₂}{a b : T₁} → ((a ▫ x) ≡ (b ▫ x)) → (a ≡ b)
  Cancellationᵣ : (T₁ → T₂ → T₃) → Stmt
  Cancellationᵣ (_▫_) = (∀{x : T₂} → CancellationOnᵣ (_▫_)(x))

---------------------------------------------------------
-- Patterns

module _ {ℓ₁ ℓ₂ ℓ₃ ℓᵣ₂ ℓᵣ₃ ℓᵣ} {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}}{T₃ : Type{ℓ₃}}{Tᵣ₂ : Type{ℓᵣ₂}}{Tᵣ₃ : Type{ℓᵣ₃}}{Tᵣ : Type{ℓᵣ}} ⦃ _ : Equiv(Tᵣ) ⦄ where
  AssociativityPattern : (T₁ → T₂ → Tᵣ₃) → (Tᵣ₃ → T₃ → Tᵣ)  → (T₁ → Tᵣ₂ → Tᵣ) → (T₂ → T₃ → Tᵣ₂)→ Stmt
  AssociativityPattern (_▫₁_) (_▫₂_) (_▫₃_) (_▫₄_) =
    ∀{x : T₁}{y : T₂}{z : T₃} → ((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z))

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv(T₃) ⦄ where
  DistributivityPatternₗ : (T₁ → T₂ → T₃) → (T₂ → T₂ → T₂) → (T₃ → T₃ → T₃) → Stmt
  DistributivityPatternₗ (_▫₁_) (_▫₂_) (_▫₃_) =
    ∀{x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ ((x ▫₁ y) ▫₃ (x ▫₁ z))

  DistributivityPatternᵣ : (T₁ → T₂ → T₃) → (T₁ → T₁ → T₁) → (T₃ → T₃ → T₃) → Stmt
  DistributivityPatternᵣ (_▫₁_) (_▫₂_) (_▫₃_) =
    ∀{x y : T₁} {z : T₂} → ((x ▫₂ y) ▫₁ z) ≡ ((x ▫₁ z) ▫₃ (y ▫₁ z))

---------------------------------------------------------
-- Derived

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ where
  -- Definition of associativity for a binary operation
  Associativity : (T → T → T) → Stmt
  Associativity (_▫_) = AssociativityPattern (_▫_) (_▫_) (_▫_) (_▫_)
  -- {x y z : T} → ((x ▫ y) ▫ z) ≡ (x ▫ (y ▫ z))

module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv(T₂) ⦄ where
  -- Definition of compatibility for a binary operation
  Compatibility : (T₁ → T₁ → T₁) → (T₁ → T₂ → T₂) → Stmt
  Compatibility (_▫₁_) (_▫₂_) = AssociativityPattern (_▫₁_) (_▫₂_) (_▫₂_) (_▫₂_)
  -- {x₁ x₂ : T₁}{y : T₂} → ((x₁ ▫₁ x₂) ▫₂ y) ≡ (x₁ ▫₂ (x₂ ▫₂ y))

  -- Definition of left distributivity for a binary operation
  Distributivityₗ : (T₁ → T₂ → T₂) → (T₂ → T₂ → T₂) → Stmt
  Distributivityₗ (_▫₁_) (_▫₂_) = DistributivityPatternₗ (_▫₁_) (_▫₂_) (_▫₂_)
  -- ∀{x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ (x ▫₁ y) ▫₂ (x ▫₁ z)

  -- Definition of right distributivity for a binary operation
  Distributivityᵣ : (T₂ → T₁ → T₂) → (T₂ → T₂ → T₂) → Stmt
  Distributivityᵣ (_▫₁_) (_▫₂_) = DistributivityPatternᵣ (_▫₁_) (_▫₂_) (_▫₂_)
  -- ∀{x y : T₂} {z : T₁} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₂ (y ▫₁ z)

---------------------------------------------------------
-- Functions
{-
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}

-- Returns a commuted LHS of an equality
commuteₗ : ∀{T}{_▫_}{x y z} → ⦃ _ : Commutativity {T} {T} (_▫_) ⦄ → ((x ▫ y) ≡ z) → ((y ▫ x) ≡ z)
commuteₗ ⦃ comm ⦄ stmt = comm 🝖 stmt

-- Returns a commuted RHS of an equality
commuteᵣ : ∀{T}{_▫_}{x y z} → ⦃ _ : Commutativity {T} {T} (_▫_) ⦄ → (z ≡ (x ▫ y)) → (z ≡ (y ▫ x))
commuteᵣ ⦃ comm ⦄ stmt = stmt 🝖 comm

commuteBoth : ∀{T₁ T₂}{_▫_}{a₁ a₂ b₁ b₂} → Commutativity{T₁}{T₂}(_▫_) → (a₁ ▫ a₂ ≡ b₁ ▫ b₂) → (a₂ ▫ a₁ ≡ b₂ ▫ b₁)
commuteBoth {_}{_} {a₁} {a₂} {b₁} {b₂} commutativity (a₁▫a₂≡b₁▫b₂) =
    (symmetry ⦃ [≡]-symmetry ⦄ (commutativity {a₁} {a₂}))
    🝖' (a₁▫a₂≡b₁▫b₂)
    🝖' (commutativity {b₁} {b₂})
    where
      _🝖'_ = _🝖_ ⦃ [≡]-transitivity ⦄
      infixl 1000 _🝖'_
-}
