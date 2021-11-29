module Structure.Relator where

import Lvl
open import Functional using (_∘₂_)
open import Functional.Dependent
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Relator.Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

-- TODO: It seems possible to define UnaryRelator as a special case of Function, so let's do that

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓₗ₄ : Lvl.Level

module Names where
  module _ {A : Type{ℓₒ}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ (P : A → Stmt{ℓₗ₂}) where
    Substitution₁ = ∀{x y : A} → (x ≡ y) → P(x) → P(y)

  module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ₃}) where
    Substitution₂ = ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)

  module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {C : Type{ℓₒ₃}} ⦃ _ : Equiv{ℓₗ₃}(C) ⦄ (_▫_▫_ : A → B → C → Stmt{ℓₗ₄}) where
    Substitution₃ = ∀{x₁ y₁ : A}{x₂ y₂ : B}{x₃ y₃ : C} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (x₁ ▫ x₂ ▫ x₃) → (y₁ ▫ y₂ ▫ y₃)

-- The unary relator `P` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ (P : A → Stmt{ℓₗ₂}) where
  record UnaryRelator : Stmt{ℓₒ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field
      substitution : Names.Substitution₁(P)
    substitution-sym : ∀{x y : A} → (x ≡ y) → P(x) ← P(y)
    substitution-sym = substitution ∘ Structure.Relator.Properties.symmetry(_≡_)
    substitution-equivalence : ∀{x y : A} → (x ≡ y) → (P(x) ↔ P(y))
    substitution-equivalence xy = [↔]-intro (substitution-sym xy) (substitution xy)
  substitute₁ₗ = inferArg UnaryRelator.substitution-sym
  substitute₁ᵣ = inferArg UnaryRelator.substitution
  substitute₁ₗᵣ = inferArg UnaryRelator.substitution-equivalence
  substitute₁ = substitute₁ᵣ
  unaryRelator = resolve UnaryRelator

-- The binary relator `_▫_` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ₃}) where
  open Structure.Relator.Properties

  record BinaryRelator : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field
      substitution : Names.Substitution₂(_▫_)
    left : ∀{x} → UnaryRelator(_▫ x)
    left = intro(\p → substitution p (reflexivity(_≡_)))
    right : ∀{x} → UnaryRelator(x ▫_)
    right = intro(\p → substitution (reflexivity(_≡_)) p)
    substitutionₗ = \{a x y} → UnaryRelator.substitution(left {a}) {x}{y}
    substitutionᵣ = \{a x y} → UnaryRelator.substitution(right{a}) {x}{y}
    substitution-sym : ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → ((x₁ ▫ x₂) ← (y₁ ▫ y₂))
    substitution-sym xy1 xy2 = substitution (Structure.Relator.Properties.symmetry(_≡_) xy1) (Structure.Relator.Properties.symmetry(_≡_) xy2)
    substitution-equivalence : ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → ((x₁ ▫ x₂) ↔ (y₁ ▫ y₂))
    substitution-equivalence xy1 xy2 = [↔]-intro (substitution-sym xy1 xy2) (substitution xy1 xy2)
  substitute₂ = inferArg BinaryRelator.substitution
  substitute₂ₗ = inferArg BinaryRelator.substitutionₗ
  substitute₂ᵣ = inferArg BinaryRelator.substitutionᵣ
  substitute₂ₗᵣ = inferArg BinaryRelator.substitution-equivalence
  binaryRelator = resolve BinaryRelator

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ {C : Type{ℓₒ₃}} ⦃ _ : Equiv{ℓₗ₃}(C) ⦄ (_▫_▫_ : A → B → C → Stmt{ℓₗ₄}) where
  open Structure.Relator.Properties

  record TrinaryRelator : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃ Lvl.⊔ ℓₗ₄} where
    constructor intro
    field
      substitution : Names.Substitution₃(_▫_▫_)
    unary₁ : ∀{y z} → UnaryRelator(_▫ y ▫ z)
    unary₁ = intro(\p → substitution p (reflexivity(_≡_)) (reflexivity(_≡_)))
    unary₂ : ∀{x z} → UnaryRelator(x ▫_▫ z)
    unary₂ = intro(\p → substitution (reflexivity(_≡_)) p (reflexivity(_≡_)))
    unary₃ : ∀{x y} → UnaryRelator(x ▫ y ▫_)
    unary₃ = intro(\p → substitution (reflexivity(_≡_)) (reflexivity(_≡_)) p)
    binary₁₂ : ∀{z} → BinaryRelator(_▫_▫ z)
    binary₁₂ = intro(\p q → substitution p q (reflexivity(_≡_)))
    binary₁₃ : ∀{y} → BinaryRelator(_▫ y ▫_)
    binary₁₃ = intro(\p q → substitution p (reflexivity(_≡_)) q)
    binary₂₃ : ∀{x} → BinaryRelator(x ▫_▫_)
    binary₂₃ = intro(\p q → substitution (reflexivity(_≡_)) p q)
    substitution-unary₁ = \{a b x y} → UnaryRelator.substitution(unary₁ {a}{b}) {x}{y}
    substitution-unary₂ = \{a b x y} → UnaryRelator.substitution(unary₂ {a}{b}) {x}{y}
    substitution-unary₃ = \{a b x y} → UnaryRelator.substitution(unary₃ {a}{b}) {x}{y}
    substitution-binary₁₂ = \{a x₁ x₂ y₁ y₂} → BinaryRelator.substitution(binary₁₂ {a}) {x₁}{x₂}{y₁}{y₂}
    substitution-binary₁₃ = \{a x₁ x₂ y₁ y₂} → BinaryRelator.substitution(binary₁₃ {a}) {x₁}{x₂}{y₁}{y₂}
    substitution-binary₂₃ = \{a x₁ x₂ y₁ y₂} → BinaryRelator.substitution(binary₂₃ {a}) {x₁}{x₂}{y₁}{y₂}
  substitute₃ = inferArg TrinaryRelator.substitution
  substitute₃-unary₁ = inferArg TrinaryRelator.substitution-unary₁
  substitute₃-unary₂ = inferArg TrinaryRelator.substitution-unary₂
  substitute₃-unary₃ = inferArg TrinaryRelator.substitution-unary₃
  substitute₃-binary₁₂ = inferArg TrinaryRelator.substitution-binary₁₂
  substitute₃-binary₁₃ = inferArg TrinaryRelator.substitution-binary₁₃
  substitute₃-binary₂₃ = inferArg TrinaryRelator.substitution-binary₂₃
  trinaryRelator = resolve TrinaryRelator
