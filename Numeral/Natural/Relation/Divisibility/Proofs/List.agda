module Numeral.Natural.Relation.Divisibility.Proofs.List where

open import Data.List.Functions as List
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Quantification
open import Logic.Propositional
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Type

divides-foldᵣ-member : ∀{_▫_}{id} → (∀{x y₁ y₂} → ((x ∣ y₁) ∨ (x ∣ y₂)) → (x ∣ (y₁ ▫ y₂))) → ∀{x}{l} → (x ∈ l) → (x ∣ List.foldᵣ(_▫_) id l)
divides-foldᵣ-member div (•_ {x}{l} p) = div {y₂ = List.foldᵣ(_) _ l} ([∨]-introₗ (sub₂(_≡_)(_∣_) p))
divides-foldᵣ-member div (⊰_ {_}{x} p) = div {y₁ = x}                 ([∨]-introᵣ (divides-foldᵣ-member div p))

divides-[⋅]-list : ∀{x}{l} → (x ∈ l) → (x ∣ List.foldᵣ(_⋅_) 1 l)
divides-[⋅]-list = divides-foldᵣ-member divides-with-[⋅]
