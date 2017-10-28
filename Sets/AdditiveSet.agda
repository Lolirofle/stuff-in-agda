module Sets.AdditiveSet {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
import      Relator.Equals{ℓ₁}{ℓ₂} as Eq
open import Type{ℓ₂}

-- TODO: Remove this? This is almost too similar to ListSet, but done badly
data AddSet(T : Type) : Type where
  ∅    : AddSet(T)
  S[_] : T → AddSet(T)
  _∪_  : AddSet(T) → AddSet(T) → AddSet(T)

module _ {T : Type} where
  _∈_ : T → AddSet(T) → Stmt
  _∈_ x ∅        = ⊥
  _∈_ x (S[ y ]) = (x Eq.≡ y)
  _∈_ x (A ∪ B)  = (x ∈ A) ∨ (x ∈ B)

  _⊆_ : AddSet(T) → AddSet(T) → Stmt
  _⊆_ A B = ∀{x} → ((x ∈ A) ← (x ∈ B))

  _⊇_ : AddSet(T) → AddSet(T) → Stmt
  _⊇_ A B = ∀{x} → ((x ∈ A) → (x ∈ B))

  _≡_ : AddSet(T) → AddSet(T) → Stmt
  _≡_ A B = ∀{x} → ((x ∈ A) ↔ (x ∈ B))

  module Theorems where
    [∪]-commutativity : ∀{A B} → (A ∪ B)≡(B ∪ A)
    [∪]-commutativity = [↔]-intro([∨]-commutativity)([∨]-commutativity)
    -- (A ∪ B)≡(B ∪ A)
    -- (x ∈ (A ∪ B)) ↔ (x ∈ (B ∪ A))
    -- ((x ∈ A) ∨ (x ∈ B)) ↔ ((x ∈ B) ∨ (x ∈ A))

    [∪]-associativity : ∀{A B C} → ((A ∪ B) ∪ C)≡(A ∪ (B ∪ C))
    [∪]-associativity = [∨]-associativity
    -- ((A ∪ B) ∪ C)≡(A ∪ (B ∪ C))
    -- (x ∈ ((A ∪ B) ∪ C)) ↔ (x ∈ (A ∪ (B ∪ C)))
    -- ((x ∈ (A ∪ B)) ∨ (x ∈ C)) ↔ ((x ∈ A) ∨ (x ∈ (B ∪ C)))
    -- (((x ∈ A) ∨ (x ∈ B)) ∨ (x ∈ C)) ↔ ((x ∈ A) ∨ ((x ∈ B) ∨ (x ∈ C)))

    [∈][≡]-elimᵣ : ∀{A B} → (A ≡ B) → ∀{x} → (x ∈ A) → (x ∈ B)
    [∈][≡]-elimᵣ(A≡B){_} = [↔]-elimᵣ(A≡B)

    [∈][≡]-elimₗ : ∀{A B} → (A ≡ B) → ∀{x} → (x ∈ B) → (x ∈ A)
    [∈][≡]-elimₗ(A≡B){_} = [↔]-elimₗ(A≡B)
