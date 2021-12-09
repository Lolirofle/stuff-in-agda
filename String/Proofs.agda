module String.Proofs where

open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import String
open import String.Functions as String hiding (module Primitives)
open import Structure.Function.Domain

module Primitives where
  primitive primStringToListInjective : ∀ a b → String.Primitives.primStringToList a ≡ String.Primitives.primStringToList b → a ≡ b
  primitive primStringFromListInjective : ∀ a b → String.Primitives.primStringFromList a ≡ String.Primitives.primStringFromList b → a ≡ b

instance
  chars-injective : Injective(chars)
  chars-injective = intro \{a b} → Primitives.primStringToListInjective a b

instance
  fromChars-injective : Injective(fromChars)
  fromChars-injective = intro \{a b} → Primitives.primStringFromListInjective a b
