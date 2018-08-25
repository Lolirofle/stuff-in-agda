module Structure.Operator.Proofs{ℓ₁}{ℓ₂} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
open import Relator.Equals.Proofs{ℓ₁}{ℓ₂}
open import Relator.Equals.Uniqueness{ℓ₁}{ℓ₂}{Lvl.𝟎}
open import Structure.Function.Domain{ℓ₁}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type

module One {T} {_▫_ : T → T → T} where
  -- When an identity element exists and is the same for both sides, it is unique.
  unique-identity : Unique(Identity(_▫_))
  unique-identity{x₁}{x₂} ([∧]-intro identityₗ₁ identityᵣ₁) ([∧]-intro identityₗ₂ identityᵣ₂) =
    symmetry(identityₗ₂{x₁})
    🝖 identityᵣ₁{x₂}

  module Commutable (commutativity : Commutativity(_▫_)) where
    -- An existing left identity is inique when the operator is commutative
    unique-identityₗ-by-commutativity : Unique(Identityₗ(_▫_))
    unique-identityₗ-by-commutativity {x₁}{x₂} (identity₁) (identity₂) =
      symmetry(identity₂{x₁})
      🝖 commutativity{x₂}{x₁}
      🝖 identity₁{x₂}

  module Cancellableᵣ (cancellation : Cancellationᵣ(_▫_)) where
    -- An existing left identity is inique when the operator is cancellable
    unique-identityₗ-by-cancellationᵣ : Unique(Identityₗ(_▫_))
    unique-identityₗ-by-cancellationᵣ {x₁}{x₂} (identity₁) (identity₂) =
      cancellation {x₁}{x₁}{x₂} (
        (identity₁{x₁}             :of: (x₁ ▫ x₁ ≡ x₁))
        🝖 (symmetry(identity₂{x₁}) :of: (x₁ ≡ x₂ ▫ x₁))
      ) :of: (x₁ ≡ x₂)

  module Cancellableₗ (cancellation : Cancellationₗ(_▫_)) where
    -- An existing left identity is inique when the operator is cancellable
    unique-identityᵣ-by-cancellationₗ : Unique(Identityᵣ(_▫_))
    unique-identityᵣ-by-cancellationₗ {x₁}{x₂} (identity₁) (identity₂) =
      cancellation {x₂}{x₁}{x₂} (
        (identity₁{x₂}             :of: (x₂ ▫ x₁ ≡ x₂))
        🝖 (symmetry(identity₂{x₂}) :of: (x₂ ≡ x₂ ▫ x₂))
      ) :of: (x₁ ≡ x₂)

  module GroupLikeₗ (associativity : Associativity(_▫_)) {id} (identity : Identityₗ(_▫_)(id)) {inv} (inverse : InverseFunctionₗ(_▫_)(id)(inv)) where
    -- Cancellation is possible when the operator is associative and have an inverse
    cancellation-by-associativity-inverse : Cancellationₗ(_▫_)
    cancellation-by-associativity-inverse {x}{a}{b} (xa≡xb) =
      symmetry(identity{a})
      🝖 [≡]-with(_▫ a) (symmetry(inverse{x}))
      🝖 associativity{inv(x)}{x}{a}
      🝖 [≡]-with(inv(x) ▫_) (xa≡xb)
      🝖 symmetry(associativity{inv(x)}{x}{b})
      🝖 [≡]-with(_▫ b) (inverse{x})
      🝖 identity{b}
      -- TODO: This pattern of applying symmetric transitivity rules, make it a function

  module GroupLike (associativity : Associativity(_▫_)) {id} (identity : Identity(_▫_)(id)) {inv} (inverse : InverseFunction(_▫_)(id)(inv)) where
    -- When something and something else's inverse is the identity element, they are equal
    equality-zeroₗ : ∀{x y} → (x ≡ y) ← (x ▫ inv(y) ≡ id)
    equality-zeroₗ {x}{y} (proof) =
      (symmetry ([∧]-elimᵣ identity)                  :of: (x ≡ x ▫ id))
      🝖 (symmetry([≡]-with(x ▫_) ([∧]-elimₗ inverse)) :of: (x ▫ id ≡ x ▫ (inv(y) ▫ y)))
      🝖 (symmetry(associativity)                      :of: (x ▫ (inv(y) ▫ y) ≡ (x ▫ inv(y)) ▫ y))
      🝖 ([≡]-with(_▫ y) (proof)                       :of: ((x ▫ inv(y)) ▫ y ≡ id ▫ y))
      🝖 ([∧]-elimₗ identity                           :of: (id ▫ y ≡ y))

  {-
  module MonoidLikeₗ (associativity : Associativity(_▫_)) {id} (identity : Identityₗ(_▫_)(id)) where
    postulate unique-inverse : Associativity(_▫_) → ∀{id} → Identity(_▫_)(id) → Unique(InverseFunctionₗ(_▫_)(id))
  -}

  module LoopLikeᵣ {id} (identity : Identityᵣ(_▫_)(id)) {inv} (inverse : InverseFunctionᵣ(_▫_)(id)(inv)) where
    -- When something and something else are equal, then the operation of the first one and the second's inverse is the identity element
    equality-zeroᵣ : ∀{x y} → (x ≡ y) → (x ▫ inv(y) ≡ id)
    equality-zeroᵣ {x}{y} (proof) =
      ([≡]-with(_▫ inv(y)) (proof) :of: (x ▫ inv(y) ≡ y ▫ inv(y)))
      🝖 (inverse                   :of: (y ▫ inv(y) ≡ id))

module Two {T₁}{T₂} {_▫₁_}{_▫₂_} {θ : T₁ → T₂} (preserving : Preserving2(θ)(_▫₁_)(_▫₂_)) where
  module Cancellableᵣ (cancellation : Cancellationᵣ(_▫₂_)) where
    module Identifiableₗ {id₁} (identity₁ : Identityₗ(_▫₁_)(id₁)) {id₂} (identity₂ : Identityₗ(_▫₂_)(id₂)) where
      preserving-identityₗ : (θ(id₁) ≡ id₂)
      preserving-identityₗ =
        (cancellation
          ((\{x} →
            (symmetry(preserving{id₁}{x}) :of: (θ(id₁) ▫₂ θ(x) ≡ θ(id₁ ▫₁ x)))
            🝖 ([≡]-with(θ) (identity₁{x}) :of: (θ(id₁ ▫₁ x) ≡ θ(x)))
            🝖 (symmetry(identity₂{θ(x)})  :of: (θ(x) ≡ id₂ ▫₂ θ(x)))
          ){id₁})
        )

      module Invertibleₗ {inv₁} (inverse₁ : InverseFunctionₗ(_▫₁_)(id₁)(inv₁)) {inv₂} (inverse₂ : InverseFunctionₗ(_▫₂_)(id₂)(inv₂)) where
        preserving-inverseₗ : ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
        preserving-inverseₗ {x} =
          (cancellation(
            (symmetry(preserving{inv₁(x)}{x}) :of: (θ(inv₁(x)) ▫₂ θ(x) ≡ θ(inv₁(x) ▫₁ x)))
            🝖 ([≡]-with(θ) (inverse₁{x})      :of: (θ(inv₁(x) ▫₁ x) ≡ θ(id₁)))
            🝖 (preserving-identityₗ            :of: (θ(id₁) ≡ id₂))
            🝖 (symmetry(inverse₂{θ(x)})       :of: (id₂ ≡ inv₂(θ(x)) ▫₂ θ(x)))
          ))

  module Cancellableₗ (cancellation : Cancellationₗ(_▫₂_)) where
    module Identifiableᵣ {id₁} (identity₁ : Identityᵣ(_▫₁_)(id₁)) {id₂} (identity₂ : Identityᵣ(_▫₂_)(id₂)) where
      preserving-identityᵣ : (θ(id₁) ≡ id₂)
      preserving-identityᵣ =
        (cancellation
          ((\{x} →
            (symmetry(preserving{x}{id₁}) :of: (θ(x) ▫₂ θ(id₁) ≡ θ(x ▫₁ id₁)))
            🝖 ([≡]-with(θ) (identity₁{x}) :of: (θ(x ▫₁ id₁) ≡ θ(x)))
            🝖 (symmetry(identity₂{θ(x)})  :of: (θ(x) ≡ θ(x) ▫₂ id₂))
          ){id₁})
        )

      module Invertibleᵣ {inv₁} (inverse₁ : InverseFunctionᵣ(_▫₁_)(id₁)(inv₁)) {inv₂} (inverse₂ : InverseFunctionᵣ(_▫₂_)(id₂)(inv₂)) where
        preserving-inverseᵣ : ∀{x} → (θ(inv₁(x)) ≡ inv₂(θ(x)))
        preserving-inverseᵣ {x} =
          (cancellation(
            (symmetry(preserving{x}{inv₁(x)}) :of: (θ(x) ▫₂ θ(inv₁(x)) ≡ θ(x ▫₁ inv₁(x))))
            🝖 ([≡]-with(θ) (inverse₁{x})      :of: (θ(x ▫₁ inv₁(x)) ≡ θ(id₁)))
            🝖 (preserving-identityᵣ            :of: (θ(id₁) ≡ id₂))
            🝖 (symmetry(inverse₂{θ(x)})       :of: (id₂ ≡ θ(x) ▫₂ inv₂(θ(x))))
          ))

  module GroupLike
    (associativity₁ : Associativity(_▫₁_))
    (associativity₂ : Associativity(_▫₂_))
    {id₁}  (identity₁ : Identity(_▫₁_)(id₁))             {id₂}  (identity₂ : Identity(_▫₂_)(id₂))
    {inv₁} (inverse₁ : InverseFunction(_▫₁_)(id₁)(inv₁)) {inv₂} (inverse₂ : InverseFunction(_▫₂_)(id₂)(inv₂))
    where

    open One.GroupLikeₗ {T₂} {_▫₂_} (associativity₂) {id₂} ([∧]-elimₗ identity₂) {inv₂} ([∧]-elimₗ inverse₂)
    open One.GroupLike {T₁} {_▫₁_} (associativity₁) {id₁} (identity₁) {inv₁} (inverse₁)
    open One.LoopLikeᵣ {T₂} {_▫₂_} {id₂} ([∧]-elimᵣ identity₂) {inv₂} ([∧]-elimᵣ inverse₂)

    open Cancellableₗ.Identifiableᵣ (cancellation-by-associativity-inverse) {id₁} ([∧]-elimᵣ identity₁) {id₂} ([∧]-elimᵣ identity₂) using (preserving-identityᵣ) public
    open Cancellableₗ.Identifiableᵣ.Invertibleᵣ (cancellation-by-associativity-inverse) {id₁} ([∧]-elimᵣ identity₁) {id₂} ([∧]-elimᵣ identity₂) {inv₁} ([∧]-elimᵣ inverse₁) {inv₂} ([∧]-elimᵣ inverse₂) public

    injective-kernelᵣ : Injective(θ) ↔ (∀{a : T₁} → (θ(a) ≡ id₂) → (a ≡ id₁))
    injective-kernelᵣ = [↔]-intro l r where
      l : Injective(θ) ← (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      l(proof) {a}{b} (θa≡θb) =
        equality-zeroₗ(
          proof(
            (preserving{a}{inv₁(b)}                       :of: (θ(a ▫₁ inv₁(b)) ≡ θ(a) ▫₂ θ(inv₁(b))))
            🝖 ([≡]-with(θ(a) ▫₂_) (preserving-inverseᵣ{b}) :of: (θ(a) ▫₂ θ(inv₁(b)) ≡ θ(a) ▫₂ inv₂(θ(b))))
            🝖 (equality-zeroᵣ(θa≡θb)                       :of: (θ(a) ▫₂ inv₂(θ(b)) ≡ id₂))
          ) :of: (a ▫₁ inv₁(b) ≡ id₁)
        ) :of: (a ≡ b)

      r : Injective(θ) → (∀{a} → (θ(a) ≡ id₂) → (a ≡ id₁))
      r(injective) {a} (θa≡id) =
        symmetry(injective{id₁}{a}(
          (preserving-identityᵣ :of: (θ(id₁) ≡ id₂))
          🝖 (symmetry(θa≡id)    :of: (id₂ ≡ θ(a)))
        ))
