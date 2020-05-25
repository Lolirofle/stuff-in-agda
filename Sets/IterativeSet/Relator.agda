module Sets.IterativeSet.Relator where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Sets.IterativeSet
open import Syntax.Function
open import Type

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level
  private variable {A B} : Iset{ℓ}
  open Iset

  _≡_ : (A : Iset{ℓ₁}) → (B : Iset{ℓ₂}) → Type{ℓ₁ Lvl.⊔ ℓ₂}
  record _⊆_ (A : Iset{ℓ₁}) (B : Iset{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂}
  _⊇_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}

  -- Set equality is by definition the antisymmetric property of the subset relation.
  _≡_ A B = (A ⊇ B) ∧ (A ⊆ B)

  -- Set membership is the existence of an index in the set that points to a set equal element to the element.
  _∈_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
  a ∈ B = ∃{Obj = Index(B)} (ib ↦ a ≡ elem(B)(ib))

  -- Set subset is a mapping between the indices such that they point to the same element in both sets.
  record _⊆_ A B where
    constructor intro
    inductive
    eta-equality
    field
      map : Index(A) → Index(B)
      proof : ∀{ia} → (elem(A)(ia) ≡ elem(B)(map(ia)))

  A ⊇ B = B ⊆ A
  module _⊇_ where
    open _⊆_ public

  _∉_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
  a ∉ B = ¬(a ∈ B)
