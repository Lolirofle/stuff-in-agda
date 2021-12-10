module Structure.Relator2 where

import      Lvl
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; swap)
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Structure.Function
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

  module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ}) where
    Substitution₂ = Congruence₂ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ (_▫_)

  module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {C : Type{ℓ₃}} ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ (_▫_▫_ : A → B → C → Stmt{ℓₗ}) where
    Substitution₃ = Congruence₃ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ (_▫_▫_)

module _ {A : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ (P : A → Stmt{ℓₗ}) where
  -- The unary relator `P` is a relator with respect to the given setoid.
  UnaryRelator = Function ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ P

  UnaryRelator-introₗ : (∀{x y} → (x ≡ y) → P(x) ← P(y)) → UnaryRelator
  UnaryRelator-introₗ p = intro(xy ↦ [↔]-intro (p xy) (p(symmetry(_≡_) xy)))
  UnaryRelator-introᵣ : (∀{x y} → (x ≡ y) → P(x) → P(y)) → UnaryRelator
  UnaryRelator-introᵣ p = intro(xy ↦ [↔]-intro (p(symmetry(_≡_) xy)) (p xy))

  substitute₁ = congruence₁ ⦃ equiv ⦄ ⦃ [↔]-equiv ⦄ P
  substitute₁ₗ = \ ⦃ inst ⦄ {x}{y} → [↔]-to-[←] ∘ substitute₁ ⦃ inst ⦄ {x}{y}
  substitute₁ᵣ = \ ⦃ inst ⦄ {x}{y} → [↔]-to-[→] ∘ substitute₁ ⦃ inst ⦄ {x}{y}

  module UnaryRelator ⦃ rel : UnaryRelator ⦄ where
    open Function(rel) using () renaming (congruence to substitution) public

module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ}) where
  -- The binary relator `P` is a relator with respect to the given setoid.
  BinaryRelator = BinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ [↔]-equiv ⦄ (_▫_)

  BinaryRelator-introₗ : (∀{x₁ y₁}{x₂ y₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) ← (y₁ ▫ y₂)) → BinaryRelator
  BinaryRelator-introₗ p = intro(xy₁ ↦ xy₂ ↦ [↔]-intro (p xy₁ xy₂) (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂)))
  BinaryRelator-introᵣ : (∀{x₁ y₁}{x₂ y₂} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)) → BinaryRelator
  BinaryRelator-introᵣ p = intro(xy₁ ↦ xy₂ ↦ [↔]-intro (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂)) (p xy₁ xy₂))

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

  BinaryRelator-unary-intro : (∀{y} → UnaryRelator(_▫ y)) → (∀{x} → UnaryRelator(x ▫_)) → BinaryRelator
  BinaryRelator-unary-intro = BinaryOperator-unary-intro(_▫_)

module _ {A : Type{ℓ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {C : Type{ℓ₃}} ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ (_▫_▫_ : A → B → C → Stmt{ℓₗ}) where
  -- The trinary relator `P` is a relator with respect to the given setoid.
  TrinaryRelator = TrinaryOperator ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ equiv-C ⦄ ⦃ [↔]-equiv ⦄ (_▫_▫_)

  TrinaryRelator-introₗ : (∀{x₁ y₁}{x₂ y₂}{x₃ y₃} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (x₁ ▫ x₂ ▫ x₃) ← (y₁ ▫ y₂ ▫ y₃)) → TrinaryRelator
  TrinaryRelator-introₗ p = intro(xy₁ ↦ xy₂ ↦ xy₃ ↦ [↔]-intro (p xy₁ xy₂ xy₃) (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂) (symmetry(_≡_) xy₃)))
  TrinaryRelator-introᵣ : (∀{x₁ y₁}{x₂ y₂}{x₃ y₃} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (x₁ ▫ x₂ ▫ x₃) → (y₁ ▫ y₂ ▫ y₃)) → TrinaryRelator
  TrinaryRelator-introᵣ p = intro(xy₁ ↦ xy₂ ↦ xy₃ ↦ [↔]-intro (p(symmetry(_≡_) xy₁) (symmetry(_≡_) xy₂) (symmetry(_≡_) xy₃)) (p xy₁ xy₂ xy₃))

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

  TrinaryRelator-unary-intro : (∀{y}{z} → Function(_▫ y ▫ z)) → (∀{x}{z} → Function(x ▫_▫ z)) → (∀{x}{y} → Function(x ▫ y ▫_)) → TrinaryRelator
  TrinaryRelator-unary-intro = TrinaryOperator-unary-intro(_▫_▫_)
