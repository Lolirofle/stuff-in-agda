module Structure.Relator where

import Lvl
open import Functional.Dependent
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Structure.Relator.Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module Names where
  module _ {A : Type{ℓₒ}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ (P : A → Stmt{ℓₗ₂}) where
    Substitution₁ = ∀{x y : A} → (x ≡ y) → P(x) → P(y)

  module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ₃}) where
    Substitution₂ = ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)

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
  substitute₁ₗ = inst-fn UnaryRelator.substitution-sym
  substitute₁ᵣ = inst-fn UnaryRelator.substitution
  substitute₁ₗᵣ = inst-fn UnaryRelator.substitution-equivalence
  substitute₁ = substitute₁ᵣ
  unaryRelator = resolve UnaryRelator

-- The binary relator `_▫_` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (_▫_ : A → B → Stmt{ℓₗ₃}) where
  open Structure.Relator.Properties

  record BinaryRelator : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₃ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field
      substitution : Names.Substitution₂(_▫_)
    left : ∀{x} → UnaryRelator(_▫ x)
    left = intro(\p → substitution p (reflexivity(_≡_)))
    right : ∀{x} → UnaryRelator(x ▫_)
    right = intro(\p → substitution (reflexivity(_≡_)) p)
    substitutionₗ = \{a x y} → UnaryRelator.substitution(left {a}) {x}{y}
    substitutionᵣ = \{a x y} → UnaryRelator.substitution(right{a}) {x}{y}
  substitute₂ = inst-fn BinaryRelator.substitution
  substitute₂ₗ = inst-fn BinaryRelator.substitutionₗ
  substitute₂ᵣ = inst-fn BinaryRelator.substitutionᵣ
  binaryRelator = resolve BinaryRelator
