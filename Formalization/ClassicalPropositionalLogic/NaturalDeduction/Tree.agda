open import Type
open import Logic.Classical as Logic using (Classical)
open import Logic.Predicate as Logic using ()

module Formalization.ClassicalPropositionalLogic.NaturalDeduction.Tree ⦃ classical : ∀{ℓ} → Logic.∀ₗ(Classical{ℓ}) ⦄ where

import      Lvl
open import Logic
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

open import Formalization.ClassicalPropositionalLogic.Syntax

module _ {ℓₚ} {P : Type{ℓₚ}} where
  {-# NO_POSITIVITY_CHECK #-}
  data Tree : Formula(P) → Stmt{Lvl.𝐒(ℓₚ)} where
    [⊤]-intro : Tree(⊤)

    [⊥]-intro : ∀{φ} → Tree(φ) → Tree(¬ φ) → Tree(⊥)
    [⊥]-elim  : ∀{φ} → Tree(⊥) → Tree(φ)

    [¬]-intro : ∀{φ} → (Tree(φ) → Tree(⊥)) → Tree(¬ φ)
    [¬]-elim  : ∀{φ} → (Tree(¬ φ) → Tree(⊥)) → Tree(φ)

    [∧]-intro : ∀{φ ψ} → Tree(φ) → Tree(ψ) → Tree(φ ∧ ψ)
    [∧]-elimₗ : ∀{φ ψ} → Tree(φ ∧ ψ) → Tree(φ)
    [∧]-elimᵣ : ∀{φ ψ} → Tree(φ ∧ ψ) → Tree(ψ)

    [∨]-introₗ : ∀{φ ψ} → Tree(φ) → Tree(φ ∨ ψ)
    [∨]-introᵣ : ∀{φ ψ} → Tree(ψ) → Tree(φ ∨ ψ)
    [∨]-elim   : ∀{φ ψ χ} → (Tree(φ) → Tree(χ)) → (Tree(ψ) → Tree(χ)) → Tree(φ ∨ ψ) → Tree(χ)

    [⟶]-intro : ∀{φ ψ} → (Tree(φ) → Tree(ψ)) → Tree(φ ⟶ ψ)
    [⟶]-elim  : ∀{φ ψ} → Tree(φ) → Tree(φ ⟶ ψ) → Tree(ψ)

    [⟷]-intro : ∀{φ ψ} → (Tree(ψ) → Tree(φ)) → (Tree(φ) → Tree(ψ)) → Tree(ψ ⟷ φ)
    [⟷]-elimₗ : ∀{φ ψ} → Tree(φ) → Tree(ψ ⟷ φ) → Tree(ψ)
    [⟷]-elimᵣ : ∀{φ ψ} → Tree(ψ) → Tree(ψ ⟷ φ) → Tree(φ)

  open import Formalization.ClassicalPropositionalLogic.NaturalDeduction

  module _ {ℓ} where
    Tree-to-[⊢]-tautologies : ∀{φ} → Tree(φ) → (∅{ℓ} ⊢ φ)
    Tree-to-[⊢]-tautologies {.⊤} [⊤]-intro = [⊤]-intro
    Tree-to-[⊢]-tautologies {.⊥} ([⊥]-intro tφ tφ₁) =
      ([⊥]-intro
        (Tree-to-[⊢]-tautologies tφ)
        (Tree-to-[⊢]-tautologies tφ₁)
      )
    Tree-to-[⊢]-tautologies {φ} ([⊥]-elim tφ) =
      ([⊥]-elim
        (Tree-to-[⊢]-tautologies tφ)
      )
    Tree-to-[⊢]-tautologies {.(¬ _)} ([¬]-intro x) = [¬]-intro {!!}
    Tree-to-[⊢]-tautologies {φ} ([¬]-elim x) = {!!}
    Tree-to-[⊢]-tautologies {.(_ ∧ _)} ([∧]-intro tφ tφ₁) =
      ([∧]-intro
        (Tree-to-[⊢]-tautologies tφ)
        (Tree-to-[⊢]-tautologies tφ₁)
      )
    Tree-to-[⊢]-tautologies {φ} ([∧]-elimₗ tφ) =
      ([∧]-elimₗ
        (Tree-to-[⊢]-tautologies tφ)
      )
    Tree-to-[⊢]-tautologies {φ} ([∧]-elimᵣ tφ) =
      ([∧]-elimᵣ
        (Tree-to-[⊢]-tautologies tφ)
      )
    Tree-to-[⊢]-tautologies {.(_ ∨ _)} ([∨]-introₗ tφ) =
      ([∨]-introₗ
        (Tree-to-[⊢]-tautologies tφ)
      )
    Tree-to-[⊢]-tautologies {.(_ ∨ _)} ([∨]-introᵣ tφ) =
      ([∨]-introᵣ
        (Tree-to-[⊢]-tautologies tφ)
      )
    Tree-to-[⊢]-tautologies {φ} ([∨]-elim x x₁ tφ) = {!!}
    Tree-to-[⊢]-tautologies {.(_ ⟶ _)} ([⟶]-intro x) = {!!}
    Tree-to-[⊢]-tautologies {φ} ([⟶]-elim tφ tφ₁) =
      ([⟶]-elim
        (Tree-to-[⊢]-tautologies tφ)
        (Tree-to-[⊢]-tautologies tφ₁)
      )
    Tree-to-[⊢]-tautologies {.(_ ⟷ _)} ([⟷]-intro x x₁) = {!!}
    Tree-to-[⊢]-tautologies {φ} ([⟷]-elimₗ tφ tφ₁) =
      ([⟷]-elimₗ
        (Tree-to-[⊢]-tautologies tφ)
        (Tree-to-[⊢]-tautologies tφ₁)
      )
    Tree-to-[⊢]-tautologies {φ} ([⟷]-elimᵣ tφ tφ₁) =
      ([⟷]-elimᵣ
        (Tree-to-[⊢]-tautologies tφ)
        (Tree-to-[⊢]-tautologies tφ₁)
      )

  --Tree-to-[⊢] : ∀{P : Type{ℓₚ}}{Γ : Formulas(P)}{φ} → ((Γ ⊆ Tree) → Tree(φ)) → (Γ ⊢ φ)
  --Tree-to-[⊢] {Γ} {φ} t = {!!}
