module Data.List.Relation where

import Lvl
open import Data.List
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

-- Statement of whether a list is contained in the beginning of another list
_isPrefixOf_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T) → Stmt
_isPrefixOf_ prefix l = (∃ \rest → l ≡ (prefix ++ rest))

-- Statement of whether a list is contained in the end of another list
_isSuffixOf_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T) → Stmt
_isSuffixOf_ suffix l = (∃ \rest → l ≡ (rest ++ suffix))
