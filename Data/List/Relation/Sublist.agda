import      Lvl
open import Type

module Data.List.Relation.Sublist {ℓ} {T : Type{ℓ}} where

open import Data.List using (List ; ∅ ; _⊰_)
open import Logic

-- Statement of whether a list's elements are contained in another list in order.
data _⊑_ : List(T) → List(T) → Stmt{ℓ} where
  instance
    empty : (∅ ⊑ ∅)
    use   : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → ((x ⊰ L₁) ⊑ (x ⊰ L₂))
    skip  : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → (L₁       ⊑ (x ⊰ L₂))
