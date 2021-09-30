import      Lvl
open import Type
open import Structure.Setoid

module Data.List.Relation.Sublist {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T)⦄ where

open import Data.List using (List ; ∅ ; _⊰_)
open import Functional
open import Logic

-- Whether a list's elements are contained in another list in order.
-- Examples:
--   [1,2,3] ⊑ [1,2,3]
--   [1,2,3] ⊑ [1,2,3,4]
--   [1,2,3] ⊑ [0,1,2,3]
--   [1,2,3] ⊑ [0,1,10,2,20,3,30]
--   [0,10,20,30] ⊑ [0,1,10,2,20,3,30]
data _⊑_ : List(T) → List(T) → Stmt{ℓ Lvl.⊔ ℓₑ} where
  empty : (∅ ⊑ ∅)
  use   : ∀{x y}{l₁ l₂} → (x ≡ y) → (l₁ ⊑ l₂) → ((x ⊰ l₁) ⊑ (y ⊰ l₂))
  skip  : ∀{x}  {l₁ l₂} →           (l₁ ⊑ l₂) → (l₁       ⊑ (x ⊰ l₂))

-- Whether a list's elements are contained in another list in order while not containing the same sublist.
-- Examples:
--   [1,2,3] ⊏ [1,2,3,4]
--   [1,2,3] ⊏ [0,1,2,3]
--   [1,2,3] ⊏ [0,1,10,2,20,3,30]
data _⊏_ : List(T) → List(T) → Stmt{ℓ Lvl.⊔ ℓₑ} where
  use   : ∀{x y}{l₁ l₂} → (x ≡ y) → (l₁ ⊏ l₂) → ((x ⊰ l₁) ⊏ (y ⊰ l₂))
  skip  : ∀{x}  {l₁ l₂} →           (l₁ ⊑ l₂) → (l₁       ⊏ (x ⊰ l₂))

_⊒_ = swap(_⊑_)
_⊐_ = swap(_⊏_)
