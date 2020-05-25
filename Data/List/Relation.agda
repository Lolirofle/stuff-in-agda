module Data.List.Relation where

import      Lvl
import      Data
open import Data.List
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}

data Empty {ℓ}{T : Type{ℓ}} : List(T) → Stmt{Lvl.𝐒(ℓ)} where
  intro : Empty(∅)

-- Statement of whether a list is contained in the beginning of another list
_isPrefixOf_ : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → List(T) → List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓₑ}
∅            isPrefixOf _       = Data.Unit
(p ⊰ prefix) isPrefixOf ∅       = Data.Empty
(p ⊰ prefix) isPrefixOf (x ⊰ l) = (p ≡ x) ∧ (prefix isPrefixOf l)
-- _isPrefixOf_ prefix l = (∃ \rest → l ≡ (prefix ++ rest))

-- Statement of whether a list is contained in the end of another list
_isSuffixOf_ : ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ → ⦃ equiv-list : Equiv{ℓₑ₂}(List(T)) ⦄ → List(T) → List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂}
∅            isSuffixOf _       = Data.Unit
(p ⊰ prefix) isSuffixOf ∅       = Data.Empty
(p ⊰ prefix) isSuffixOf (x ⊰ l) = ((p ⊰ prefix) isSuffixOf l) ∨ ((p ⊰ prefix) ≡ (x ⊰ l))
-- _isSuffixOf_ suffix l = (∃ \rest → l ≡ (rest ++ suffix))
