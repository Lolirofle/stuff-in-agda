module Structure.Relator2 where

import      Lvl
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; swap)
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

  module BinaryRelator ⦃ rel : BinaryRelator ⦄ where
    open BinaryOperator(rel) using () renaming (congruence to substitution) public

    unary₁ : ∀{b} → UnaryRelator(_▫ b)
    unary₁ = intro(swap substitute₂(reflexivity(_≡_)))

    unary₂ : ∀{a} → UnaryRelator(a ▫_)
    unary₂ = intro(substitute₂(reflexivity(_≡_)))

  module _ ⦃ rel : BinaryRelator ⦄ where
    substitute₂-₁ = \b {x}{y} → UnaryRelator.substitution ⦃ rel = BinaryRelator.unary₁{b} ⦄ {x}{y}
    substitute₂-₂ = \b {x}{y} → UnaryRelator.substitution ⦃ rel = BinaryRelator.unary₂{b} ⦄ {x}{y}

  BinaryRelator-unary-intro : (∀{b} → UnaryRelator(_▫ b)) → (∀{a} → UnaryRelator(a ▫_)) → BinaryRelator
  BinaryRelator-unary-intro unary₁ unary₂ = intro(xy₁ ↦ xy₂ ↦ transitivity(_≡_) (Function.congruence unary₁ xy₁) (Function.congruence unary₂ xy₂))

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

  module TrinaryRelator ⦃ rel : TrinaryRelator ⦄ where
    open TrinaryOperator(rel) using () renaming (congruence to substitution) public

    unary₁ : ∀{b}{c} → UnaryRelator(_▫ b ▫ c)
    unary₁ = intro(p₁ ↦ substitute₃ p₁ (reflexivity(_≡_)) (reflexivity(_≡_)))

    unary₂ : ∀{a}{c} → UnaryRelator(a ▫_▫ c)
    unary₂ = intro(p₂ ↦ substitute₃(reflexivity(_≡_)) p₂ (reflexivity(_≡_)))

    unary₃ : ∀{a}{b} → UnaryRelator(a ▫ b ▫_)
    unary₃ = intro(p₃ ↦ substitute₃(reflexivity(_≡_)) (reflexivity(_≡_)) p₃)

    binary₁,₂ : ∀{c} → BinaryRelator(_▫_▫ c)
    binary₁,₂ = intro(p₁ ↦ p₂ ↦ substitute₃ p₁ p₂ (reflexivity(_≡_)))

    binary₁,₃ : ∀{b} → BinaryRelator(_▫ b ▫_)
    binary₁,₃ = intro(p₁ ↦ p₃ ↦ substitute₃ p₁ (reflexivity(_≡_)) p₃)

    binary₂,₃ : ∀{a} → BinaryRelator(a ▫_▫_)
    binary₂,₃ = intro(p₂ ↦ p₃ ↦ substitute₃ (reflexivity(_≡_)) p₂ p₃)

  module _ ⦃ rel : TrinaryRelator ⦄ where
    substitute₃-₁ = \b c {x}{y} → UnaryRelator.substitution ⦃ rel = TrinaryRelator.unary₁{b}{c} ⦄ {x}{y}
    substitute₃-₂ = \a c {x}{y} → UnaryRelator.substitution ⦃ rel = TrinaryRelator.unary₂{a}{c} ⦄ {x}{y}
    substitute₃-₃ = \a b {x}{y} → UnaryRelator.substitution ⦃ rel = TrinaryRelator.unary₃{a}{b} ⦄ {x}{y}

    substitute₃-₁,₂ = \c {x₁}{y₁}{x₂}{y₂} → BinaryRelator.substitution ⦃ rel = TrinaryRelator.binary₁,₂{c} ⦄ {x₁}{y₁}{x₂}{y₂}
    substitute₃-₁,₃ = \b {x₁}{y₁}{x₂}{y₂} → BinaryRelator.substitution ⦃ rel = TrinaryRelator.binary₁,₃{b} ⦄ {x₁}{y₁}{x₂}{y₂}
    substitute₃-₂,₃ = \a {x₁}{y₁}{x₂}{y₂} → BinaryRelator.substitution ⦃ rel = TrinaryRelator.binary₂,₃{a} ⦄ {x₁}{y₁}{x₂}{y₂}

  TrinaryRelator-unary-intro : (∀{b}{c} → UnaryRelator(_▫ b ▫ c)) → (∀{a}{c} → UnaryRelator(a ▫_▫ c)) → (∀{a}{b} → UnaryRelator(a ▫ b ▫_)) → TrinaryRelator
  TrinaryRelator-unary-intro unary₁ unary₂ unary₃ = intro(xy₁ ↦ xy₂ ↦ xy₃ ↦ transitivity(_≡_) (Function.congruence unary₁ xy₁) (transitivity(_≡_) (Function.congruence unary₂ xy₂) (Function.congruence unary₃ xy₃)))
