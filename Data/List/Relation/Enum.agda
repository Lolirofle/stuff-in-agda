module Data.List.Relation.Enum where

open import Data.List
open import Data.List.Relation.Membership hiding (_≡_)
open import Functional
open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

-- A list is an enumeration when it contains all the inhabitants of its type.
-- Note: Duplicates are allowed in the list. The only guarantee is that the list is complete.
-- Also called: Listable.
Enumeration : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → List(T) → Type
Enumeration = ∀ₗ ∘ (_∋_)

-- A type is enumerable when there is an enumeration.
Enumerable : (T : Type{ℓ}) → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Type
Enumerable T = ∃(Enumeration{T = T})

enum : (T : Type{ℓ}) → ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → ⦃ enum : Enumerable(T) ⦄ → List(T)
enum _ ⦃ enum = p ⦄ = [∃]-witness p

enum-enumeration : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → ⦃ enum : Enumerable(T) ⦄ → Enumeration(_)
enum-enumeration ⦃ enum = p ⦄ = [∃]-proof p
