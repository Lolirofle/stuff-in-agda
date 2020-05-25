import      Lvl
open import Logic
open import Type

module Data.List.Relation.OrderedPairwise {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where

open import Data.List
import      Data.List.Functions as List

-- Statement for when a list's elements in order pairwise satisfy a binary relation.
data OrderedPairwise : List(T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  instance
    empty  : OrderedPairwise(∅)
    single : ∀{a} → OrderedPairwise(List.singleton(a))
    step   : ∀{a b}{l} → ⦃ _ : (a ▫ b) ⦄ → ⦃ _ : OrderedPairwise(b ⊰ l) ⦄ → OrderedPairwise(a ⊰ b ⊰ l)
