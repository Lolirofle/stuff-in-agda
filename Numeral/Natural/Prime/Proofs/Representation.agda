module Numeral.Natural.Prime.Proofs.Representation where

-- TODO: Clean up the import list
import      Lvl
open import Data
open import Data.Either as Either using ()
open import Data.Tuple as Tuple using (_,_)
open import Functional
open import Function.Equals
open import Lang.Instance
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.CoordinateVector
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Product
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Equivalence.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_ ; _≢_ to _≢ₛ_)
open import Structure.Setoid.Uniqueness
open import Syntax.Transitivity
open import Type
open import Type.Dependent

private variable a b : ℕ

open import Logic.Classical
open import Numeral.Natural.Decidable

open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Prime.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Structure.Relator.Ordering

open import Data.List
open import Data.List.Equiv.Id
open import Data.List.Functions as List using (_++_)
open import Numeral.Natural.Oper.Proofs
open import Structure.Operator

open import Structure.Operator.Properties

open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Classical
open import Syntax.Implication
open import Type.Properties.Decidable.Proofs

-- Note: This proof is very similar to the proof of prime factor existence (prime-factor-existence).
prime-representation-existence : ∀{n} → ∃{Obj = List(∃ Prime)}(l ↦ (𝐒(𝐒 n) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
prime-representation-existence {n} = Strict.Properties.wellfounded-induction(_<_) {P = \n → ∃(l ↦ (𝐒(𝐒(n)) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))} rec {n} where
  rec : ∀{n} → ({prev : ℕ} ⦃ _ : prev < n ⦄ → ∃(l ↦ (𝐒(𝐒 prev) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))) → ∃(l ↦ (𝐒(𝐒 n) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
  rec {n} prev with prime-or-composite{𝐒(𝐒(n))}
  ... | Either.Left  p = [∃]-intro (List.singleton([∃]-intro _ ⦃ p ⦄)) ⦃ [≡]-intro ⦄
  ... | Either.Right c
    with [∃]-intro(a , b) ⦃ p ⦄ ← [↔]-to-[→] composite-existence c
    with [∃]-intro da ⦃ pa ⦄ ← prev{a} ⦃ [≤]-without-[𝐒] ([≤]-without-[𝐒] (subtransitivityᵣ(_≤_)(_≡_) ([⋅]ₗ-strictly-growing {𝐒 a}{𝐒(𝐒(b))} (succ (succ min))) p)) ⦄
    with [∃]-intro db ⦃ pb ⦄ ← prev{b} ⦃ [≤]-without-[𝐒] ([≤]-without-[𝐒] (subtransitivityᵣ(_≤_)(_≡_) ([⋅]ₗ-strictly-growing {𝐒 b}{𝐒(𝐒(a))} (succ (succ min))) (commutativity(_⋅_) {𝐒(𝐒 b)}{𝐒(𝐒 a)} 🝖 p))) ⦄
    = [∃]-intro (da List.++ db) ⦃ pab ⦄ where
      pab =
        𝐒(𝐒 n)                                                                      🝖[ _≡_ ]-[ p ]-sym
        𝐒(𝐒 a) ⋅ 𝐒(𝐒 b)                                                             🝖[ _≡_ ]-[ congruence₂(_⋅_) pa pb ]
        (List.foldᵣ((_⋅_) ∘ ∃.witness) 1 da) ⋅ (List.foldᵣ((_⋅_) ∘ ∃.witness) 1 db) 🝖[ _≡_ ]-[ foldᵣ-preserves-[++] {_▫₁_ = (_⋅_) ∘ [∃]-witness}{_▫₂_ = _⋅_}{1} {da}{db} (\{x}{y}{z} → associativity(_⋅_) {[∃]-witness x}{y}{z})  ]-sym
        List.foldᵣ((_⋅_) ∘ ∃.witness) 1 (da List.++ db)                             🝖-end

open import Data.List.Relation.Permutation

-- TODO: Are there any easy ways to prove that two lists permutes each other?
-- TODO: Probably should include some kind of reasoning for ((a ▫ b ≡ id) → ((a ≡ id) ∨ (b ≡ id))) and of course, commutativity of (_▫_).
postulate product-permutation : ∀{ℓ}{T : Type{ℓ}}{_▫_ : T → T → T}{id}{a b} → (List.foldᵣ(_▫_) id a ≡ List.foldᵣ(_▫_) id b) → (a permutes b)
-- product-permutation{_▫_ = _▫_}{id}{a}{b} = ?
{-product-permutation {a = ∅} {b = ∅} p = _permutes_.empty
product-permutation {a = ∅} {b = b ⊰ bl} p = {!!}
product-permutation {a = a ⊰ al} {b = ∅} p = {!!}
product-permutation {a = a ⊰ al} {b = b ⊰ bl} p = {!!}
-}

postulate prime-representation-uniqueness : ∀{n} → Unique{Obj = List(∃ Prime)} ⦃ Proofs.permutes-equiv ⦄ (l ↦ (𝐒(𝐒 n) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))

-- Each positive number have a corresponding finite multiset of prime numbers such that it is equal to the product of the numbers in the multiset.
-- Examples:
--   n = (p₁ ^ n₁) ⋅ (p₂ ^ n₂) ⋅ … ⋅ (pₖ ^ nₖ)
-- Also called:
-- • Fundamental theorem of arithmetic.
-- • Canonical representation of positive integers by primes.
-- • Unique prime factorization theorem.
prime-representation : ∀{n} → ∃!{Obj = List(∃ Prime)} ⦃ Proofs.permutes-equiv ⦄ (l ↦ (𝐒(𝐒 n) ≡ List.foldᵣ((_⋅_) ∘ [∃]-witness) 𝟏 l))
prime-representation = [∧]-intro prime-representation-existence prime-representation-uniqueness

-- TODO: This also means that this is a bijection between List(∃ Prime) and ℕ, and also between List(ℕ) and ℕ if one is successful in proving that there are countably infinite many primes (a constructive proof of the latter)
