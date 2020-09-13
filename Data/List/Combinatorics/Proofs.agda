module Data.List.Combinatorics.Proofs where

import      Lvl
open import Data
open import Data.List
open import Data.List.Combinatorics
open import Data.List.Functions
open import Data.List.Relation.Quantification
open import Data.List.Relation.Sublist
open import Data.List.Relation.Sublist.Proofs
open import Data.List.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Data.Tuple.Raiseᵣ as Tuple₊
import      Data.Tuple.Raiseᵣ.Functions as Tuple₊
open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Combinatorics
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l : List(T)
private variable x : T
private variable n k : ℕ

{- TODO: Not sure how to prove this. Maybe by proving that the inductive case of sublists₊ is a permutation of something that easier to prove
sublists₊-contains-sublists : AllElements (_⊑ l) (sublists₊(l))
sublists₊-contains-sublists {l = ∅} = ∅
sublists₊-contains-sublists {l = x ⊰ l} = use [⊑]-minimum ⊰ {!!}
-}

sublists₊-length : length(sublists₊ l) ≡ (2 ^ (length l)) −₀ 1
sublists₊-length {l = ∅} = [≡]-intro
sublists₊-length {l = x ⊰ l} =
  length(sublists₊ (x ⊰ l)) 🝖[ _≡_ ]-[]
  length(singleton(x) ⊰ foldᵣ (prev ↦ rest ↦ (prev ⊰ (x ⊰ prev) ⊰ rest)) ∅ (sublists₊ l)) 🝖[ _≡_ ]-[]
  𝐒(length(foldᵣ (prev ↦ rest ↦ (prev ⊰ (x ⊰ prev) ⊰ rest)) ∅ (sublists₊ l)))             🝖[ _≡_ ]-[ [≡]-with(𝐒) (length-foldᵣ {l = sublists₊(l)}{init = ∅}{f = (prev ↦ rest ↦ (prev ⊰ (x ⊰ prev) ⊰ rest))}{g = const(𝐒 ∘ 𝐒)} [≡]-intro) ]
  𝐒(foldᵣ (prev ↦ rest ↦ 𝐒(𝐒(rest))) 𝟎 (sublists₊ l))                                     🝖[ _≡_ ]-[ [≡]-with(𝐒) (foldᵣ-constant-[+]ᵣ{l = sublists₊ l}{init = 𝟎}) ]
  𝐒(2 ⋅ length(sublists₊ l))     🝖[ _≡_ ]-[ [≡]-with(𝐒 ∘ (2 ⋅_)) (sublists₊-length {l = l}) ]
  𝐒(2 ⋅ (2 ^ (length l) −₀ 1))   🝖[ _≡_ ]-[ [≡]-with(𝐒) (distributivityₗ(_⋅_)(_−₀_) {2}{2 ^ length(l)}{1}) ]
  𝐒((2 ⋅ (2 ^ (length l))) −₀ 2) 🝖[ _≡_ ]-[]
  𝐒((2 ^ 𝐒(length l)) −₀ 2)      🝖[ _≡_ ]-[]
  𝐒((2 ^ length(x ⊰ l)) −₀ 2)    🝖[ _≡_ ]-[ [↔]-to-[→] [−₀][𝐒]ₗ-equality ([^]ₗ-strictly-growing {0}{0}{𝐒(length l)} [≤]-with-[𝐒]) ]-sym
  𝐒(2 ^ length(x ⊰ l)) −₀ 2      🝖[ _≡_ ]-[]
  (2 ^ length (x ⊰ l)) −₀ 1      🝖-end

sublists-length : length(sublists l) ≡ 2 ^ (length l)
sublists-length {l = l} =
  length(sublists l)      🝖[ _≡_ ]-[]
  length(∅ ⊰ sublists₊ l) 🝖[ _≡_ ]-[]
  𝐒(length(sublists₊ l))  🝖[ _≡_ ]-[ [≡]-with(𝐒) (sublists₊-length {l = l}) ]
  𝐒((2 ^ length(l)) −₀ 1) 🝖[ _≡_ ]-[ [↔]-to-[→] [−₀][𝐒]ₗ-equality ([^]ₗ-growing {2}{0}{length l} [≤]-minimum) ]-sym
  𝐒(2 ^ length(l)) −₀ 1   🝖[ _≡_ ]-[]
  2 ^ length(l)           🝖-end

postulate combinations-length : length(combinations k l) ≡ 𝑐𝐶(length(l))(k)

postulate repeatableCombinations-length : length(repeatableCombinations k l) ≡ 𝑐𝐶((length(l) + k) −₀ 1)(k)

tuples-length : length(tuples n l) ≡ length(l) ^ n
tuples-length {0} = [≡]-intro
tuples-length {1} = [≡]-intro
tuples-length {𝐒(𝐒(n))}{l = ∅} = [≡]-intro
tuples-length {𝐒(𝐒(n))}{l = x ⊰ l} =
  length(tuples(𝐒(𝐒(n))) (x ⊰ l))                                                   🝖[ _≡_ ]-[]
  length(concatMap(y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))) (x ⊰ l))          🝖[ _≡_ ]-[ length-concatMap {l = x ⊰ l}{f = y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l))} ]
  foldᵣ((_+_) ∘ length ∘ (y ↦ map (y Tuple₊.⊰_) (tuples (𝐒(n)) (x ⊰ l)))) 𝟎 (x ⊰ l) 🝖[ _≡_ ]-[ foldᵣ-function₊-raw {l₁ = x ⊰ l}{a₁ = 𝟎} (\{a b} → [≡]-with(_+ b) (length-map{f = a Tuple₊.⊰_}{x = tuples (𝐒(n)) (x ⊰ l)})) [≡]-intro [≡]-intro ]
  foldᵣ((_+_) ∘ length ∘ (y ↦ tuples (𝐒(n)) (x ⊰ l))) 𝟎 (x ⊰ l)                     🝖[ _≡_ ]-[]
  foldᵣ(const(length(tuples (𝐒(n)) (x ⊰ l)) +_)) 𝟎 (x ⊰ l)                          🝖[ _≡_ ]-[ foldᵣ-constant-[+]ₗ{l = x ⊰ l} {init = 𝟎}{step = length(tuples (𝐒(n)) (x ⊰ l))} ]
  length(x ⊰ l) ⋅ length(tuples(𝐒(n)) (x ⊰ l))                                      🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_) (length(x ⊰ l)) (tuples-length {𝐒(n)} {l = x ⊰ l}) ]
  length(x ⊰ l) ⋅ (length(x ⊰ l) ^ 𝐒(n))                                            🝖[ _≡_ ]-[]
  length(x ⊰ l) ^ 𝐒(𝐒(n))                                                           🝖-end

postulate rotations-length : length(rotations l) ≡ length(l)

postulate insertedEverywhere-length : length(insertedEverywhere x l) ≡ 𝐒(length(l))

postulate permutations-length : length(permutations l) ≡ length(l) !
