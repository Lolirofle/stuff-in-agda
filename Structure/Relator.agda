module Structure.Relator where

import      Lvl
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; swap ; _→ᶠ_)
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Structure.Function hiding (Compatible₁)
open import Structure.Function.Names
open import Structure.Operator
open import Structure.Setoid
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level

module Names where
  module _ {A : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ (P : A → Stmt{ℓₗ}) where
    Substitution₁ = Congruence₁ ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ P
    Substitution₁ₗ = Compatible₁(_≡_ ⦃ equiv ⦄)(_←_) P
    Substitution₁ᵣ = Compatible₁(_≡_ ⦃ equiv ⦄)(_→ᶠ_) P

  module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ}) where
    Substitution₂ = Congruence₂ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ (_▫_)
    Substitution₂ₗ = Compatible₂(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄)(_←_) (_▫_)
    Substitution₂ᵣ = Compatible₂(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄)(_→ᶠ_) (_▫_)

  module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {C : Type{ℓ₃}} ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ (_▫_▫_ : A → B → C → Stmt{ℓₗ}) where
    Substitution₃ = Congruence₃ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ (_▫_▫_)
    Substitution₃ₗ = Compatible₃(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄)(_≡_ ⦃ equiv-C ⦄)(_←_) (_▫_▫_)
    Substitution₃ᵣ = Compatible₃(_≡_ ⦃ equiv-A ⦄)(_≡_ ⦃ equiv-B ⦄)(_≡_ ⦃ equiv-C ⦄)(_→ᶠ_) (_▫_▫_)

module _ {A : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ where
  module _ (P : A → Stmt{ℓₗ}) where
    -- The unary relator `P` is a relator with respect to the given setoid.
    UnaryRelator = Function ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ P

    substitute₁ = congruence₁ ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ P
    substitute₁ₗ = \ ⦃ inst ⦄ {x}{y} → [↔]-to-[←] ∘ substitute₁ ⦃ inst ⦄ {x}{y}
    substitute₁ᵣ = \ ⦃ inst ⦄ {x}{y} → [↔]-to-[→] ∘ substitute₁ ⦃ inst ⦄ {x}{y}

    module UnaryRelator = Function ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ {P}
      renaming (congruence to substitution)

  module _ {P : A → Stmt{ℓₗ}} where
    UnaryRelator-introₗ : (∀{x y} → (x ≡ y) → P(x) ← P(y)) → UnaryRelator(P)
    UnaryRelator-introₗ p = intro(xy ↦ [↔]-intro (p xy) (p(symmetry(_≡_) xy)))
    UnaryRelator-introᵣ : (∀{x y} → (x ≡ y) → P(x) → P(y)) → UnaryRelator(P)
    UnaryRelator-introᵣ p = intro(xy ↦ [↔]-intro (p(symmetry(_≡_) xy)) (p xy))

module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  module _ (_▫_ : A → B → Stmt{ℓₗ}) where
    -- The binary relator `P` is a relator with respect to the given setoid.
    BinaryRelator = BinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ (_▫_)

    substitute₂ = congruence₂ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ (_▫_)
    substitute₂ₗ = \ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂} → [↔]-to-[←] ∘₂ substitute₂ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}
    substitute₂ᵣ = \ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂} → [↔]-to-[→] ∘₂ substitute₂ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}

    module BinaryRelator = BinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ {_▫_}
      renaming (
        congruence  to substitution ;
        congruence₁ to substitution₁ ;
        congruence₂ to substitution₂
      )

    BinaryRelator-unary₁ = inferArg BinaryRelator.unary₁
    BinaryRelator-unary₂ = inferArg BinaryRelator.unary₂

    substitute₂-₁ = inferArg BinaryRelator.substitution₁
    substitute₂-₂ = inferArg BinaryRelator.substitution₂
    substitute₂-₁ₗ = \ ⦃ inst ⦄ a {x}{y} → [↔]-to-[←] ∘ substitute₂-₁ ⦃ inst ⦄ a {x}{y}
    substitute₂-₁ᵣ = \ ⦃ inst ⦄ a {x}{y} → [↔]-to-[→] ∘ substitute₂-₁ ⦃ inst ⦄ a {x}{y}
    substitute₂-₂ₗ = \ ⦃ inst ⦄ a {x}{y} → [↔]-to-[←] ∘ substitute₂-₂ ⦃ inst ⦄ a {x}{y}
    substitute₂-₂ᵣ = \ ⦃ inst ⦄ a {x}{y} → [↔]-to-[→] ∘ substitute₂-₂ ⦃ inst ⦄ a {x}{y}

  module _ {_▫_ : A → B → Stmt{ℓₗ}} where
    BinaryRelator-unary-intro : (∀{y} → UnaryRelator(_▫ y)) → (∀{x} → UnaryRelator(x ▫_)) → BinaryRelator(_▫_)
    BinaryRelator-unary-intro = BinaryOperator-unary-intro(_▫_)

    BinaryRelator-introₗ : (∀{x₁ y₁}{x₂ y₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) ← (y₁ ▫ y₂)) → BinaryRelator(_▫_)
    BinaryRelator-introₗ p = intro(xy₁ ↦ xy₂ ↦ [↔]-intro (p xy₁ xy₂) (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂)))
    BinaryRelator-introᵣ : (∀{x₁ y₁}{x₂ y₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)) → BinaryRelator(_▫_)
    BinaryRelator-introᵣ p = intro(xy₁ ↦ xy₂ ↦ [↔]-intro (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂)) (p xy₁ xy₂))

module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {C : Type{ℓ₃}} ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ where
  module _ (_▫_▫_ : A → B → C → Stmt{ℓₗ}) where
    -- The trinary relator `P` is a relator with respect to the given setoid.
    TrinaryRelator = TrinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ (_▫_▫_)

    substitute₃ = congruence₃ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ (_▫_▫_)
    substitute₃ₗ = \ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}{x₃}{y₃} → [↔]-to-[←] ∘₃ substitute₃ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}{x₃}{y₃}
    substitute₃ᵣ = \ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}{x₃}{y₃} → [↔]-to-[→] ∘₃ substitute₃ ⦃ inst ⦄ {x₁}{y₁}{x₂}{y₂}{x₃}{y₃}

    module TrinaryRelator = TrinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ {_▫_▫_}
      renaming (
        congruence    to substitution ;
        congruence₁   to substitution₁ ;
        congruence₂   to substitution₂ ;
        congruence₃   to substitution₃ ;
        congruence₁,₂ to substitution₁,₂ ;
        congruence₁,₃ to substitution₁,₃ ;
        congruence₂,₃ to substitution₂,₃
      )

    TrinaryRelator-unary₁    = inferArg TrinaryRelator.unary₁
    TrinaryRelator-unary₂    = inferArg TrinaryRelator.unary₂
    TrinaryRelator-unary₃    = inferArg TrinaryRelator.unary₃
    TrinaryRelator-binary₁,₂ = inferArg TrinaryRelator.binary₁,₂
    TrinaryRelator-binary₁,₃ = inferArg TrinaryRelator.binary₁,₃
    TrinaryRelator-binary₂,₃ = inferArg TrinaryRelator.binary₂,₃

    substitute₃-₁   = inferArg TrinaryRelator.substitution₁
    substitute₃-₂   = inferArg TrinaryRelator.substitution₂
    substitute₃-₃   = inferArg TrinaryRelator.substitution₃
    substitute₃-₁,₂ = inferArg TrinaryRelator.substitution₁,₂
    substitute₃-₁,₃ = inferArg TrinaryRelator.substitution₁,₃
    substitute₃-₂,₃ = inferArg TrinaryRelator.substitution₂,₃

  module _ {_▫_▫_ : A → B → C → Stmt{ℓₗ}} where
    TrinaryRelator-introₗ : (∀{x₁ y₁}{x₂ y₂}{x₃ y₃} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (x₁ ▫ x₂ ▫ x₃) ← (y₁ ▫ y₂ ▫ y₃)) → TrinaryRelator(_▫_▫_)
    TrinaryRelator-introₗ p = intro(xy₁ ↦ xy₂ ↦ xy₃ ↦ [↔]-intro (p xy₁ xy₂ xy₃) (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂) (symmetry(_≡_) xy₃)))
    TrinaryRelator-introᵣ : (∀{x₁ y₁}{x₂ y₂}{x₃ y₃} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (x₁ ▫ x₂ ▫ x₃) → (y₁ ▫ y₂ ▫ y₃)) → TrinaryRelator(_▫_▫_)
    TrinaryRelator-introᵣ p = intro(xy₁ ↦ xy₂ ↦ xy₃ ↦ [↔]-intro (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂) (symmetry(_≡_) xy₃)) (p xy₁ xy₂ xy₃))

    TrinaryRelator-unary-intro : (∀{y}{z} → Function(_▫ y ▫ z)) → (∀{x}{z} → Function(x ▫_▫ z)) → (∀{x}{y} → Function(x ▫ y ▫_)) → TrinaryRelator(_▫_▫_)
    TrinaryRelator-unary-intro = TrinaryOperator-unary-intro(_▫_▫_)
