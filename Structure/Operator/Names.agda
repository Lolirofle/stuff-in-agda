module Structure.Operator.Names where

open import DependentFunctional
open import Function.Names
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Function.Names
open import Structure.Setoid
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓ₁ ℓ₂ ℓ₃ ℓᵣ₂ ℓᵣ₃ ℓᵣ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑᵣ : Lvl.Level

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ where
  -- Definition of commutativity of specific elements.
  -- The binary operation swapped yields the same result.
  -- Example: For any x, (x ▫ x) always commutes.
  Commuting : (T₁ → T₁ → T₂) → T₁ → T₁ → Stmt
  Commuting(_▫_) = pointwise₂,₂(_≡_) (_▫_) (swap(_▫_))

  -- Definition of commutativity.
  -- Order of application for the operation does not matter for equality.
  -- Example: Addition of the natural numbers (_+_ : ℕ → ℕ → ℕ).
  Commutativity : (T₁ → T₁ → T₂) → Stmt
  Commutativity = ∀² ∘ Commuting

  -- Definition of an left identity element.
  -- Example: Top implies a proposition in boolean logic (⊤ →_).
  Identityₗ : (T₁ → T₂ → T₂) → T₁ → Stmt
  Identityₗ (_▫_) id = ∀¹(Fixpoint(id ▫_))

  -- Definition of a right absorber element
  -- Also called "right neutral element" or "right annihilator"
  -- Applying the operation on this element to the right always yields itself.
  -- Example: A proposition implies top in boolean logic (_→ ⊤).
  Absorberᵣ : (T₁ → T₂ → T₂) → T₂ → Stmt
  Absorberᵣ (_▫_) null = ∀{x : T₁} → (x ▫ null) ≡ null

  ConverseAbsorberᵣ : (T₁ → T₂ → T₂) → T₂ → Stmt
  ConverseAbsorberᵣ (_▫_)(a) = ∀{x y} → (x ▫ y ≡ a) → (y ≡ a)

  Anticommutativity : (T₁ → T₁ → T₂) → (T₂ → T₂) → Stmt
  Anticommutativity(_▫_)(inv) = ∀{x y} → (x ▫ y ≡ inv(y ▫ x))

module _ {T₁ : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ {T₂ : Type{ℓ₂}} where
  -- Definition of an right identity element
  -- Example: Subtracting 0 for integers (_− 0).
  Identityᵣ : (T₁ → T₂ → T₁) → T₂ → Stmt
  Identityᵣ(_▫_) id = Identityₗ(swap(_▫_)) id

  -- Definition of a left absorber element
  -- Also called "left neutral element" or "left annihilator"
  -- Example: Subtraction (monus) of 0 for natural numbers (0 − ).
  Absorberₗ : (T₁ → T₂ → T₁) → T₁ → Stmt
  Absorberₗ(_▫_) null = Absorberᵣ(swap(_▫_)) null

  ConverseAbsorberₗ : (T₁ → T₂ → T₁) → T₁ → Stmt
  ConverseAbsorberₗ (_▫_)(a) = ∀{x y} → (x ▫ y ≡ a) → (x ≡ a)

module _ {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  -- Definition of an identity element
  -- Example: 0 for addition of integers, 1 for multiplication of integers.
  Identity : (T → T → T) → T → Stmt
  Identity (_▫_) id = (Identityₗ (_▫_) id) ∧ (Identityᵣ (_▫_) id)

  -- Definition of idempotence.
  Idempotence : (T → T → T) → Stmt
  Idempotence (_▫_) = ∀{x : T} → (x ▫ x ≡ x)

  -- Example: 0 for addition of natural numbers, 1 for multiplication of natural numbers.
  ConverseAbsorber : (T → T → T) → T → Stmt
  ConverseAbsorber (_▫_)(a) = ∀{x y} → (x ▫ y ≡ a) → (x ≡ a)∧(y ≡ a)

  -- Example: 0 for multiplication of natural numbers.
  WeakConverseAbsorber : (T → T → T) → T → Stmt
  WeakConverseAbsorber (_▫_)(a) = ∀{x y} → (x ▫ y ≡ a) → (x ≡ a)∨(y ≡ a)

module _ {T₊ : Type{ℓ₁}} {T₋ : Type{ℓ₂}} {Tᵣ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑᵣ}(Tᵣ) ⦄ where
  -- Definition of a left inverse element.
  InverseElementₗ : (T₋ → T₊ → Tᵣ) → Tᵣ → T₊ → T₋ → Stmt
  InverseElementₗ (_▫_) id x x⁻¹ = ((x⁻¹ ▫ x) ≡ id)

  -- Definition of a right inverse element
  InverseElementᵣ : (T₊ → T₋ → Tᵣ) → Tᵣ → T₊ → T₋ → Stmt
  InverseElementᵣ (_▫_) id x x⁻¹ = ((x ▫ x⁻¹) ≡ id)

  -- Definition of a left inverse function
  InverseFunctionₗ : (T₋ → T₊ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
  InverseFunctionₗ (_▫_) id inv = ∀{x : T₊} → InverseElementₗ(_▫_) id x (inv x)

  -- Definition of a right inverse function
  InverseFunctionᵣ : (T₊ → T₋ → Tᵣ) → Tᵣ → (T₊ → T₋) → Stmt
  InverseFunctionᵣ (_▫_) id inv = ∀{x : T₊} → InverseElementᵣ(_▫_) id x (inv x)

module _ {T : Type{ℓ₁}} {Tᵣ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑᵣ}(Tᵣ) ⦄ where
  -- Definition of an invertible element
  InverseElement : (T → T → Tᵣ) → Tᵣ → T → T → Stmt
  InverseElement (_▫_) id x x⁻¹ = (InverseElementₗ(_▫_) id x x⁻¹) ∧ (InverseElementᵣ(_▫_) id x x⁻¹)

  -- Definition of a function which returns the inverse element of the other side of the operation
  InverseFunction : (T → T → Tᵣ) → Tᵣ → (T → T) → Stmt
  InverseFunction (_▫_) id inv = (InverseFunctionₗ (_▫_) id inv) ∧ (InverseFunctionᵣ (_▫_) id inv)

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ where
  -- Definition of right cancellation of a specific object
  -- ∀{a b : T₂} → ((x ▫ a) ≡ (x ▫ b)) → (a ≡ b)
  CancellationOnₗ : (T₁ → T₂ → T₃) → T₁ → Stmt
  CancellationOnₗ (_▫_) (x) = Injective(x ▫_)

  -- Definition of left cancellation (Injectivity for the right param)
  -- ∀{x : T₁}{a b : T₂} → ((x ▫ a) ≡ (x ▫ b)) → (a ≡ b)
  Cancellationₗ : (T₁ → T₂ → T₃) → Stmt
  Cancellationₗ (_▫_) = (∀{x : T₁} → CancellationOnₗ(_▫_)(x))

module _ {T₁ : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ where
  -- Definition of right cancellation of a specific object
  -- ∀{a b : T₁} → ((a ▫ x) ≡ (b ▫ x)) → (a ≡ b)
  CancellationOnᵣ : (T₁ → T₂ → T₃) → T₂ → Stmt
  CancellationOnᵣ (_▫_) (x) = Injective(_▫ x)

  -- Definition of right cancellation (Injectivity for the left param)
  -- ∀{x : T₂}{a b : T₁} → ((a ▫ x) ≡ (b ▫ x)) → (a ≡ b)
  Cancellationᵣ : (T₁ → T₂ → T₃) → Stmt
  Cancellationᵣ (_▫_) = (∀{x : T₂} → CancellationOnᵣ (_▫_)(x))

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ where
  -- Definition of the left inverse property
  InverseOperatorOnₗ : (T₁ → T₂ → T₃) → (T₁ → T₃ → T₂) → T₁ → T₂ → Stmt
  InverseOperatorOnₗ (_▫₁_) (_▫₂_) x y = (x ▫₂ (x ▫₁ y) ≡ y)

  InverseOperatorₗ : (T₁ → T₂ → T₃) → (T₁ → T₃ → T₂) → Stmt
  InverseOperatorₗ (_▫₁_)(_▫₂_) = ∀{x y} → InverseOperatorOnₗ(_▫₁_)(_▫₂_) x y

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ where
  -- Definition of the right inverse property
  InverseOperatorOnᵣ : (T₁ → T₂ → T₃) → (T₃ → T₂ → T₁) → T₁ → T₂ → Stmt
  InverseOperatorOnᵣ (_▫₁_) (_▫₂_) x y = ((x ▫₁ y) ▫₂ y ≡ x)

  InverseOperatorᵣ : (T₁ → T₂ → T₃) → (T₃ → T₂ → T₁) → Stmt
  InverseOperatorᵣ (_▫₁_)(_▫₂_) = ∀{x y} → InverseOperatorOnᵣ(_▫₁_)(_▫₂_) x y

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ where
  InversePropertyₗ : (T₁ → T₂ → T₂) → (T₁ → T₁) → Stmt
  InversePropertyₗ (_▫_) inv = InverseOperatorₗ(_▫_)(a ↦ b ↦ inv(a) ▫ b)

  InversePropertyᵣ : (T₂ → T₁ → T₂) → (T₁ → T₁) → Stmt
  InversePropertyᵣ (_▫_) inv = InverseOperatorᵣ(_▫_)(a ↦ b ↦ a ▫ inv(b))

---------------------------------------------------------
-- Patterns

module _ {T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}}{T₃ : Type{ℓ₃}}{Tᵣ₂ : Type{ℓᵣ₂}}{Tᵣ₃ : Type{ℓᵣ₃}}{Tᵣ : Type{ℓᵣ}} ⦃ _ : Equiv{ℓₑᵣ}(Tᵣ) ⦄ where
  AssociativeOnPattern : (T₁ → T₂ → Tᵣ₃) → (Tᵣ₃ → T₃ → Tᵣ)  → (T₁ → Tᵣ₂ → Tᵣ) → (T₂ → T₃ → Tᵣ₂) → T₁ → T₂ → T₃ → Stmt
  AssociativeOnPattern (_▫₁_) (_▫₂_) (_▫₃_) (_▫₄_) x y z = ((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z))

  AssociativityPattern : (T₁ → T₂ → Tᵣ₃) → (Tᵣ₃ → T₃ → Tᵣ)  → (T₁ → Tᵣ₂ → Tᵣ) → (T₂ → T₃ → Tᵣ₂)→ Stmt
  AssociativityPattern (_▫₁_) (_▫₂_) (_▫₃_) (_▫₄_) = ∀{x : T₁}{y : T₂}{z : T₃} → AssociativeOnPattern (_▫₁_) (_▫₂_) (_▫₃_) (_▫₄_) x y z

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₃}(T₃) ⦄ where
  DistributiveOnPatternₗ : (T₁ → T₂ → T₃) → (T₂ → T₂ → T₂) → (T₃ → T₃ → T₃) → T₁ → T₂ → T₂ → Stmt
  DistributiveOnPatternₗ (_▫₁_) (_▫₂_) (_▫₃_) x y z = (x ▫₁ (y ▫₂ z)) ≡ ((x ▫₁ y) ▫₃ (x ▫₁ z))

  DistributiveOnPatternᵣ : (T₁ → T₂ → T₃) → (T₁ → T₁ → T₁) → (T₃ → T₃ → T₃) → T₁ → T₁ → T₂ → Stmt
  DistributiveOnPatternᵣ (_▫₁_) (_▫₂_) (_▫₃_) x y z = ((x ▫₂ y) ▫₁ z) ≡ ((x ▫₁ z) ▫₃ (y ▫₁ z))

  DistributivityPatternₗ : (T₁ → T₂ → T₃) → (T₂ → T₂ → T₂) → (T₃ → T₃ → T₃) → Stmt
  DistributivityPatternₗ (_▫₁_) (_▫₂_) (_▫₃_) = ∀{x : T₁} {y z : T₂} → DistributiveOnPatternₗ (_▫₁_) (_▫₂_) (_▫₃_) x y z

  DistributivityPatternᵣ : (T₁ → T₂ → T₃) → (T₁ → T₁ → T₁) → (T₃ → T₃ → T₃) → Stmt
  DistributivityPatternᵣ (_▫₁_) (_▫₂_) (_▫₃_) = ∀{x y : T₁} {z : T₂} → DistributiveOnPatternᵣ (_▫₁_) (_▫₂_) (_▫₃_) x y z

---------------------------------------------------------
-- Derived

module _ {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  AssociativeOn : (T → T → T) → T → T → T → Stmt
  AssociativeOn (_▫_) = AssociativeOnPattern (_▫_) (_▫_) (_▫_) (_▫_)

  -- Definition of associativity for a binary operation
  Associativity : (T → T → T) → Stmt
  Associativity (_▫_) = AssociativityPattern (_▫_) (_▫_) (_▫_) (_▫_)
  -- {x y z : T} → ((x ▫ y) ▫ z) ≡ (x ▫ (y ▫ z))

  Alternativeₗ : (T → T → T) → Stmt
  Alternativeₗ(_▫_) = ∀{x y} → AssociativeOnPattern(_▫_)(_▫_)(_▫_)(_▫_) x x y
  -- ∀{x y} → ((x ▫ x) ▫ y ≡ x ▫ (x ▫ y))

  Alternativeᵣ : (T → T → T) → Stmt
  Alternativeᵣ(_▫_) = ∀{x y} → AssociativeOnPattern(_▫_)(_▫_)(_▫_)(_▫_) x y y
  -- ∀{x y} → ((x ▫ y) ▫ y ≡ x ▫ (y ▫ y))

  Flexibility : (T → T → T) → Stmt
  Flexibility(_▫_) = ∀{x y} → AssociativeOnPattern(_▫_)(_▫_)(_▫_)(_▫_) x y x
  -- ∀{x y} → ((x ▫ y) ▫ x ≡ x ▫ (y ▫ x))

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ where
  -- Definition of compatibility for a binary operation
  Compatibility : (T₁ → T₁ → T₁) → (T₁ → T₂ → T₂) → Stmt -- TODO: https://en.wikipedia.org/wiki/Semigroup_action
  Compatibility (_▫₁_) (_▫₂_) = AssociativityPattern (_▫₁_) (_▫₂_) (_▫₂_) (_▫₂_)
  -- {x₁ x₂ : T₁}{y : T₂} → ((x₁ ▫₁ x₂) ▫₂ y) ≡ (x₁ ▫₂ (x₂ ▫₂ y))

  DistributiveOnₗ : (T₁ → T₂ → T₂) → (T₂ → T₂ → T₂) → T₁ → T₂ → T₂ → Stmt
  DistributiveOnₗ (_▫₁_) (_▫₂_) = DistributiveOnPatternₗ(_▫₁_)(_▫₂_)(_▫₂_)

  DistributiveOnᵣ : (T₂ → T₁ → T₂) → (T₂ → T₂ → T₂) → T₂ → T₂ → T₁ → Stmt
  DistributiveOnᵣ (_▫₁_) (_▫₂_) = DistributiveOnPatternᵣ(_▫₁_)(_▫₂_)(_▫₂_)

  -- Definition of left distributivity for a binary operation
  Distributivityₗ : (T₁ → T₂ → T₂) → (T₂ → T₂ → T₂) → Stmt
  Distributivityₗ (_▫₁_) (_▫₂_) = DistributivityPatternₗ(_▫₁_)(_▫₂_)(_▫₂_)
  -- ∀{x : T₁} {y z : T₂} → (x ▫₁ (y ▫₂ z)) ≡ (x ▫₁ y) ▫₂ (x ▫₁ z)

  -- Definition of right distributivity for a binary operation
  Distributivityᵣ : (T₂ → T₁ → T₂) → (T₂ → T₂ → T₂) → Stmt
  Distributivityᵣ (_▫₁_) (_▫₂_) = DistributivityPatternᵣ(_▫₁_)(_▫₂_)(_▫₂_)
  -- ∀{x y : T₂} {z : T₁} → ((x ▫₂ y) ▫₁ z) ≡ (x ▫₁ z) ▫₂ (y ▫₁ z)

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₁}(T₁) ⦄ where
  -- Definition of left absorption for two binary operators
  Absorptionₗ : (T₁ → T₃ → T₁) → (T₁ → T₂ → T₃) → Stmt
  Absorptionₗ (_▫₁_)(_▫₂_) = ∀{x : T₁}{y : T₂} → (x ▫₁ (x ▫₂ y) ≡ x)

module _ {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} ⦃ _ : Equiv{ℓₑ₂}(T₂) ⦄ where
  -- Definition of right absorption for two binary operators
  Absorptionᵣ : (T₃ → T₂ → T₂) → (T₁ → T₂ → T₃) → Stmt
  Absorptionᵣ (_▫₁_)(_▫₂_) = ∀{x : T₁}{y : T₂} → ((x ▫₂ y) ▫₁ y ≡ y)
