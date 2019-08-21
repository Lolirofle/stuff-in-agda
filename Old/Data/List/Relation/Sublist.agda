import      Lvl
open import Type

module Data.List.Relation.Sublist {ℓ₁ ℓ₂ : Lvl.Level} (T : Type{ℓ₂}) where

open import Data.List
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}

-- Statement of whether a list's elements are contained in another list in order.
data _⊑_ : List{ℓ₂}(T) → List{ℓ₂}(T) → Stmt where
  instance
    empty : (∅ ⊑ ∅)
    use   : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → ((x ⊰ L₁) ⊑ (x ⊰ L₂))
    skip  : ∀{x}{L₁ L₂} → (L₁ ⊑ L₂) → (L₁       ⊑ (x ⊰ L₂))
