import      Lvl
open import Type

module Data.List.Relation.Sublist {ℓ} {T : Type{ℓ}} where

open import Data.List using (List ; ∅ ; _⊰_)
open import Logic

-- Whether a list's elements are contained in another list in order.
-- Examples:
--   [1,2,3] ⊑ [1,2,3]
--   [1,2,3] ⊑ [1,2,3,4]
--   [1,2,3] ⊑ [0,1,2,3]
--   [1,2,3] ⊑ [0,1,10,2,20,3,30]
--   [0,10,20,30] ⊑ [0,1,10,2,20,3,30]
data _⊑_ : List(T) → List(T) → Stmt{ℓ} where
  empty : (∅ ⊑ ∅)
  use   : ∀{x}{l₁ l₂} → (l₁ ⊑ l₂) → ((x ⊰ l₁) ⊑ (x ⊰ l₂))
  skip  : ∀{x}{l₁ l₂} → (l₁ ⊑ l₂) → (l₁       ⊑ (x ⊰ l₂))

-- Whether a list's elements are contained in another list in order while not containing the same sublist.
-- Examples:
--   [1,2,3] ⊏ [1,2,3,4]
--   [1,2,3] ⊏ [0,1,2,3]
--   [1,2,3] ⊏ [0,1,10,2,20,3,30]
data _⊏_ : List(T) → List(T) → Stmt{ℓ} where
  use   : ∀{x}{l₁ l₂} → (l₁ ⊏ l₂) → ((x ⊰ l₁) ⊏ (x ⊰ l₂))
  skip  : ∀{x}{l₁ l₂} → (l₁ ⊑ l₂) → (l₁       ⊏ (x ⊰ l₂))
