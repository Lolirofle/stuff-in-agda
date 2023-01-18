module Structure.Operator.Proofs.ListFoldPermutation where

import      Lvl
-- open import Data.Either as Either using ()
-- open import Data.Tuple as Tuple using (_,_)
-- open import Function.Equals
-- open import Functional.Instance
-- open import Logic.Predicate
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
-- open import Structure.Relator.Equivalence.Proofs.On₂
open import Structure.Relator.Properties
-- open import Structure.Setoid renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
-- open import Structure.Setoid.Uniqueness
open import Syntax.Transitivity
open import Type
-- open import Type.Dependent.Sigma

-- open import Logic.Classical

-- open import Structure.Relator.Ordering

open import Data.List
-- open import Data.List.Equiv.Id
open import Data.List.Functions as List using (_++_)

open import Structure.Operator

open import Structure.Operator.Properties

-- open import Syntax.Implication
-- open import Type.Properties.Decidable.Proofs

open import Data.List.Relation.Permutation

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable _▫_ _▫⁻¹_ : A → B → C
private variable id x y z a b c : T
private variable l la lb lc : List(T)

{- TODO: Try to generalize foldᵣ-primes-permutation
-- TODO: Are there any easy ways to prove that two lists permutes each other?
-- TODO: Probably should include some kind of assumption of ((a ▫ b ≡ id) → ((a ≡ id) ∨ (b ≡ id))) and of course, commutativity associativity of (_▫_). Maybe assume some kind of ring?

module _
  ⦃ comm : Commutativity(_▫_) ⦄
  ⦃ assoc : Associativity(_▫_) ⦄
  ⦃ inverseOper : InverseOperatorᵣ(_▫_)(_▫⁻¹_) ⦄
  where

  ((List.foldᵣ(_▫_) id l) ▫⁻¹ x ≡ List.foldᵣ(_▫_) id (filterFirst(x ==_) l)) → (x ∈ l)

  foldᵣ-permutation : (List.foldᵣ(_▫_) id a ≡ List.foldᵣ(_▫_) id b) → (a permutes b)
  -- foldᵣ-permutation{_▫_ = _▫_}{id}{a}{b} = ?
  foldᵣ-permutation {a = ∅}      {b = ∅}      p = _permutes_.empty
  foldᵣ-permutation {a = ∅}      {b = b ⊰ bl} p = {!!}
  foldᵣ-permutation {a = a ⊰ al} {b = bl}     p = {!Strict.Properties.accessible-induction(_∣≢_) {P = _permutes (b ⊰ bl)}!}
-}

module _
  ⦃ comm : Commutativity(_▫_) ⦄
  ⦃ assoc : Associativity(_▫_) ⦄
  where

  foldᵣ-permutationₗ : (List.foldᵣ(_▫_) id a ≡ List.foldᵣ(_▫_) id b) ← (a permutes b)
  foldᵣ-permutationₗ _permutes_.empty       = reflexivity(_≡_)
  foldᵣ-permutationₗ (prepend {x = x} perm) = congruence₂-₂(_▫_)(x) (foldᵣ-permutationₗ perm)
  foldᵣ-permutationₗ {id} (swap{x = x}{y = y}{l}) =
    List.foldᵣ(_▫_) id (x ⊰ y ⊰ l)   🝖[ _≡_ ]-[]
    x ▫ (y ▫ (List.foldᵣ(_▫_) id l)) 🝖[ _≡_ ]-[ associativity(_▫_) ]-sym
    (x ▫ y) ▫ (List.foldᵣ(_▫_) id l) 🝖[ _≡_ ]-[ congruence₂-₁(_▫_)(_) (commutativity(_▫_)) ]
    (y ▫ x) ▫ (List.foldᵣ(_▫_) id l) 🝖[ _≡_ ]-[ associativity(_▫_) ]
    y ▫ (x ▫ (List.foldᵣ(_▫_) id l)) 🝖[ _≡_ ]-[]
    List.foldᵣ(_▫_) id (y ⊰ x ⊰ l)   🝖-end
  foldᵣ-permutationₗ (trans perm₁ perm₂) = foldᵣ-permutationₗ perm₁ 🝖 foldᵣ-permutationₗ perm₂
