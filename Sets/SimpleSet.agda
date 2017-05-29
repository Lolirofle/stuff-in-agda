module Sets.SimpleSet {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

data SSet(T : Type) : Type where
  ∅ : SSet(T)
  S[_] : T → SSet(T)
  _∪_ : SSet(T) → SSet(T) → SSet(T)
  _∩_ : SSet(T) → SSet(T) → SSet(T)

module _ {T : Type} where
  _∈_ : T → SSet(T) → Stmt
  _∈_ x ∅        = ⊥
  _∈_ x (S[ y ]) = (x ≡ y)
  _∈_ x (A ∪ B)  = (x ∈ A) ∨ (x ∈ B)
  _∈_ x (A ∩ B)  = (x ∈ A) ∧ (x ∈ B)

  _⊆_ : SSet(T) → SSet(T) → Stmt
  _⊆_ A B = ∀{x} → ((x ∈ A) ← (x ∈ B))

  postulate SSet-[≡]-intro : {A : SSet(T)} → {B : SSet(T)} → (A ⊆ B)∧(B ⊆ A) → (A ≡ B)

-- [∪]-commutativity : ∀{A B} → (A ∪ B)≡(B ∪ A)
