import      Lvl
open import Logic
open import Type

module Data.List.Relation.Pairwise {ℓ₁ ℓ₂} {T : Type{ℓ₁}} where

open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Quantification
open import Functional
open import Logic.Propositional

-- Whether a list's elements pairwise satisfy a binary relation with their adjacent elements in the list.
-- Example:
--   AdjacentlyPairwise(_▫_) [a,b,c,d,e]
--   ↔ (∧){
--     • (a ▫ b)
--     • (b ▫ c)
--     • (c ▫ d)
--     • (d ▫ e)
--   }
-- Note: Equivalent to OrderedPairwise(_▫_) when (_▫_) is transitive.
-- Note: Equivalent to OrderedPairwise₌(_▫_) when (_▫_) is transitive and reflexive.
-- Note: Equivalent to Pairwise(_▫_) when (_▫_) is transitive, symmetric and reflexive.
data AdjacentlyPairwise(_▫_ : T → T → Stmt{ℓ₂}) : List(T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  empty  : AdjacentlyPairwise(_▫_)(∅)
  single : ∀{a} → AdjacentlyPairwise(_▫_)(List.singleton(a))
  step   : ∀{a b}{l} → (a ▫ b) → AdjacentlyPairwise(_▫_)(b ⊰ l) → AdjacentlyPairwise(_▫_)(a ⊰ b ⊰ l)

-- Whether a list's elements pairwise satisfy a binary relation with all the successive elements in the list.
-- Length as a list of (_▫_)-inhabitants: if n>0 then (n−1)! else 0
-- Example:
--   OrderedPairwise(_▫_) [a,b,c,d,e]
--   ↔ (∧){
--     • (a ▫ b)
--     • (a ▫ c)
--     • (a ▫ d)
--     • (a ▫ e)
--     • (b ▫ c)
--     • (b ▫ d)
--     • (b ▫ e)
--     • (c ▫ d)
--     • (c ▫ e)
--     • (d ▫ e)
--   }
-- Note: Equivalent to OrderedPairwise₌(_▫_) when (_▫_) is reflexive.
-- Note: Equivalent to Pairwise(_▫_) when (_▫_) is symmetric and reflexive.
data OrderedPairwise(_▫_ : T → T → Stmt{ℓ₂}) : List(T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  empty  : OrderedPairwise(_▫_)(∅)
  step   : ∀{a}{l} → AllElements(a ▫_)(l) → OrderedPairwise(_▫_)(l) → OrderedPairwise(_▫_)(a ⊰ l)

-- Whether a list's elements pairwise satisfy a binary relation with itself and all the successive elements in the list.
-- Length as a list of (_▫_)-inhabitants: if n>0 then n! else 0
-- Example:
--   OrderedPairwise₌(_▫_) [a,b,c,d,e]
--   ↔ (∧){
--     • (a ▫ a)
--     • (a ▫ b)
--     • (a ▫ c)
--     • (a ▫ d)
--     • (a ▫ e)
--     • (b ▫ b)
--     • (b ▫ c)
--     • (b ▫ d)
--     • (b ▫ e)
--     • (c ▫ c)
--     • (c ▫ d)
--     • (c ▫ e)
--     • (d ▫ d)
--     • (d ▫ e)
--     • (e ▫ e)
--   }
-- Note: Equivalent to Pairwise(_▫_) when (_▫_) is symmetric.
data OrderedPairwise₌(_▫_ : T → T → Stmt{ℓ₂}) : List(T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  empty  : OrderedPairwise₌(_▫_)(∅)
  step   : ∀{a}{l} → AllElements(a ▫_)(a ⊰ l) → OrderedPairwise₌(_▫_)(l) → OrderedPairwise₌(_▫_)(a ⊰ l)

-- Whether a list's elements pairwise satisfy a binary relation with all the elements in the list.
-- Length as a list of (_▫_)-inhabitants: n²
-- Example:
--   Pairwise(_▫_) [a,b,c,d,e]
--   ↔ (∧){
--     • (a ▫ a)
--     • (a ▫ b)
--     • (a ▫ c)
--     • (a ▫ d)
--     • (a ▫ e)
--     • (b ▫ a)
--     • (b ▫ b)
--     • (b ▫ c)
--     • (b ▫ d)
--     • (b ▫ e)
--     • (c ▫ a)
--     • (c ▫ b)
--     • (c ▫ c)
--     • (c ▫ d)
--     • (c ▫ e)
--     • (d ▫ a)
--     • (d ▫ b)
--     • (d ▫ c)
--     • (d ▫ d)
--     • (d ▫ e)
--     • (e ▫ a)
--     • (e ▫ b)
--     • (e ▫ c)
--     • (e ▫ d)
--     • (e ▫ e)
--   }
Pairwise : (T → T → Stmt{ℓ₂}) → List(T) → Stmt
Pairwise(_▫_) l = AllElements(y ↦ AllElements(x ↦ x ▫ y)(l))(l)
