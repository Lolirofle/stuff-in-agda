module List.Relation {ℓ₁} {ℓ₂} where

import Lvl
open import List
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- Statement of whether a list is contained in the beginning of another list
_isPrefixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isPrefixOf_ prefix l = (∃ \rest → l ≡ (prefix ++ rest))

-- Statement of whether a list is contained in the end of another list
_isSuffixOf_ : ∀{T} → List(T) → List(T) → Stmt
_isSuffixOf_ suffix l = (∃ \rest → l ≡ (rest ++ suffix))
