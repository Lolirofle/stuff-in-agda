module Data.List.Combinatorics.Proofs where

import      Lvl
open import Data
open import Data.List
open import Data.List.Combinatorics
open import Data.List.Functions hiding (skip) renaming (module LongOper to List)
open        Data.List.Functions.LongOper
open import Data.List.Relation.Permutation
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
open import Numeral.Natural.Combinatorics.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l : List(T)
private variable x : T
private variable n k : ℕ

sublists₊-contains-sublists : AllElements (_⊑ l) (sublists₊(l))
sublists₊-contains-sublists {l = ∅} = ∅
sublists₊-contains-sublists {l = x ⊰ l} with sublists₊(l) | sublists₊-contains-sublists {l = l}
... | ∅       | _       = use [⊑]-minimum ⊰ ∅
... | sx ⊰ sl | px ⊰ pl = use [⊑]-minimum ⊰ skip px ⊰ use px ⊰ p pl where
  p : ∀{x : T}{l}{sl} → AllElements (_⊑ l) sl → AllElements (_⊑ (x ⊰ l)) (concatMap(y ↦ y ⊰ (x ⊰ y) ⊰ ∅) sl)
  p {sl = ∅}     ∅            = ∅
  p {sl = _ ⊰ _} (sll ⊰ alsl) = (skip sll) ⊰ (use sll) ⊰ (p alsl)

{-
sublists₊-contains-all-nonempty-sublists : ∀{x}{l₁ l₂ : List(T)} → (x ⊰ l₁ ⊑ l₂) → ExistsElement (_≡ x ⊰ l₁) (sublists(l₂))
sublists₊-contains-all-nonempty-sublists {l₁ = l₁} {prepend x l₂} (use p) = ⊰ (• {!!})
sublists₊-contains-all-nonempty-sublists {l₁ = l₁} {prepend x l₂} (skip p) = ⊰ (⊰ {!sublists₊-contains-all-nonempty-sublists ?!})

sublists-contains-all-sublists : ∀{l₁ l₂ : List(T)} → (l₁ ⊑ l₂) → ExistsElement (_≡ l₁) (sublists(l₂))
sublists-contains-all-sublists {l₁ = ∅} {∅} _⊑_.empty = • [≡]-intro
sublists-contains-all-sublists {l₁ = ∅} {prepend x l₂} (skip sub) = • [≡]-intro
sublists-contains-all-sublists {l₁ = prepend x l₁} {prepend .x l₂} (use sub) = ⊰ (⊰ {!!})
sublists-contains-all-sublists {l₁ = prepend x l₁} {prepend x₁ l₂} (skip sub) = {!!}
-}

postulate permutations-contains-permutations : AllElements (_permutes l) (permutations(l))
{-permutations-contains-permutations {l = ∅} = _permutes_.empty ⊰ ∅
permutations-contains-permutations {l = x ⊰ ∅} = _permutes_.prepend _permutes_.empty ⊰ ∅
permutations-contains-permutations {l = x ⊰ y ⊰ l} = {!!}-}

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

combinations-length : length(combinations k l) ≡ 𝑐𝐶(length(l))(k)
combinations-length {0}   {l = _} = [≡]-intro
combinations-length {𝐒 k} {l = ∅} = [≡]-intro
combinations-length {1}   {l = x ⊰ l} =
  length(combinations 1 (x ⊰ l))    🝖[ _≡_ ]-[]
  length(x ⊰ l)                     🝖[ _≡_ ]-[]
  𝐒(length l)                       🝖[ _≡_ ]-[ 𝑐𝐶-singleton-subsets ]-sym
  𝐒(𝑐𝐶 (length l) 1)                🝖[ _≡_ ]-[]
  1 + 𝑐𝐶 (length l) 1               🝖[ _≡_ ]-[]
  𝑐𝐶 (length l) 0 + 𝑐𝐶 (length l) 1 🝖[ _≡_ ]-[]
  𝑐𝐶 (𝐒(length l)) 1                🝖[ _≡_ ]-[]
  𝑐𝐶 (length(x ⊰ l)) 1              🝖-end
combinations-length {𝐒(𝐒 k)} {l = x ⊰ l} =
  length(combinations (𝐒(𝐒 k)) (x ⊰ l))                                       🝖[ _≡_ ]-[]
  length(map (x ,_) (combinations (𝐒 k) l) ++ combinations (𝐒(𝐒 k)) l)        🝖[ _≡_ ]-[ length-[++] {l₁ = map (x ,_) (combinations (𝐒 k) l)}{l₂ = combinations (𝐒(𝐒 k)) l} ]
  length(map (x ,_) (combinations (𝐒 k) l)) + length(combinations (𝐒(𝐒 k)) l) 🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(length(combinations (𝐒(𝐒 k)) l)) (length-map{f = (x ,_)}{x = combinations (𝐒 k) l}) ]
  length(combinations (𝐒 k) l) + length(combinations (𝐒(𝐒 k)) l)              🝖[ _≡_ ]-[ congruence₂(_+_) (combinations-length {𝐒 k} {l = l}) (combinations-length {𝐒(𝐒 k)} {l = l}) ]
  𝑐𝐶(length(l))(𝐒 k) + 𝑐𝐶(length(l))(𝐒(𝐒 k))                                  🝖[ _≡_ ]-[]
  𝑐𝐶 (length(x ⊰ l)) (𝐒(𝐒 k))                                                 🝖-end

repeatableCombinations-length : length(repeatableCombinations k l) ≡ 𝑐𝐶((length(l) + k) −₀ 1)(k)
repeatableCombinations-length {0}      {l = _} = [≡]-intro
repeatableCombinations-length {1}      {l = x ⊰ l} = [≡]-intro
repeatableCombinations-length {𝐒 k}    {l = ∅} = symmetry(_≡_) (𝑐𝐶-larger-subsets{k}{𝐒(k)} (reflexivity(_≤_)))
repeatableCombinations-length {𝐒(𝐒 k)} {l = x ⊰ l} =
  length (repeatableCombinations (𝐒(𝐒 k)) (x ⊰ l))                                                        🝖[ _≡_ ]-[]
  length(map(x ,_) (repeatableCombinations (𝐒 k) (x ⊰ l)) ++ repeatableCombinations(𝐒(𝐒 k)) l)            🝖[ _≡_ ]-[ length-[++] {l₁ = map(x ,_) (repeatableCombinations (𝐒 k) (x ⊰ l))}{l₂ = repeatableCombinations(𝐒(𝐒 k)) l} ]
  length(map(x ,_) (repeatableCombinations (𝐒 k) (x ⊰ l))) + length(repeatableCombinations(𝐒(𝐒 k)) l)     🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(length(repeatableCombinations(𝐒(𝐒 k)) l)) (length-map {f = x ,_}{x = repeatableCombinations (𝐒 k) (x ⊰ l)}) ]
  length(repeatableCombinations (𝐒 k) (x ⊰ l))             + length(repeatableCombinations(𝐒(𝐒 k)) l)     🝖[ _≡_ ]-[ congruence₂(_+_) (repeatableCombinations-length{k = 𝐒 k}{l = x ⊰ l}) (repeatableCombinations-length{k = 𝐒(𝐒 k)}{l = l}) ]
  𝑐𝐶((length(x ⊰ l) + 𝐒(k)) −₀ 1)(𝐒(k))                    + 𝑐𝐶((length(l) + 𝐒(𝐒(k))) −₀ 1)(𝐒(𝐒(k)))      🝖[ _≡_ ]-[]
  𝑐𝐶((length(x ⊰ l) + 𝐒(𝐒 k)) −₀ 1) (𝐒(𝐒 k))                                                              🝖-end

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

rotations-length : length(rotations l) ≡ length(l)
rotations-length{l = l} = length-accumulateIterate₀{f = rotateₗ(1)}{init = l}

insertedEverywhere-length : length(insertedEverywhere x l) ≡ 𝐒(length(l))
insertedEverywhere-length {x = x} {∅}     = [≡]-intro
insertedEverywhere-length {x = x} {a ⊰ l} =
  length(insertedEverywhere x (a ⊰ l))                                  🝖[ _≡_ ]-[]
  length((x ⊰ a ⊰ l) ⊰ (map (List.prepend a) (insertedEverywhere x l))) 🝖[ _≡_ ]-[]
  𝐒(length(map (List.prepend a) (insertedEverywhere x l)))              🝖[ _≡_ ]-[ [≡]-with(𝐒) (length-map{f = List.prepend a}{x = insertedEverywhere x l}) ]
  𝐒(length(insertedEverywhere x l))                                     🝖[ _≡_ ]-[ [≡]-with(𝐒) (insertedEverywhere-length {x = x} {l}) ]
  𝐒(𝐒(length(l)))                                                       🝖[ _≡_ ]-[]
  𝐒(length(a ⊰ l))                                                      🝖-end

postulate permutation-length : AllElements(p ↦ length p ≡ length l) (permutations l)

postulate permutations-length : length(permutations l) ≡ length(l) !
{-permutations-length {l = ∅} = [≡]-intro
permutations-length {l = x ⊰ ∅} = [≡]-intro
permutations-length {l = x ⊰ y ⊰ l} with permutations(y ⊰ l) | permutations-length {l = y ⊰ l}
... | ∅       | p = {!!}
... | z ⊰ pyl | p =
  length(foldᵣ((_++_) ∘ insertedEverywhere x) ∅ (z ⊰ pyl))                            🝖[ _≡_ ]-[]
  length(insertedEverywhere x z ++ foldᵣ((_++_) ∘ insertedEverywhere x) ∅ pyl)        🝖[ _≡_ ]-[ length-[++] {l₁ = insertedEverywhere x z}{l₂ = foldᵣ((_++_) ∘ insertedEverywhere x) ∅ pyl} ]
  length(insertedEverywhere x z) + length(foldᵣ((_++_) ∘ insertedEverywhere x) ∅ pyl) 🝖[ _≡_ ]-[ congruence₂ₗ(_+_)(length(foldᵣ((_++_) ∘ insertedEverywhere x) ∅ pyl)) (insertedEverywhere-length {x = x}{l = z}) ]
  𝐒(length z)                    + length(foldᵣ((_++_) ∘ insertedEverywhere x) ∅ pyl) 🝖[ _≡_ ]-[ {!!} ]
  𝐒(𝐒(length l)) ⋅ 𝐒(length pyl)                                                      🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(𝐒(𝐒(length l))) p ]
  𝐒(𝐒(length l)) ⋅ (𝐒(length l) ⋅ (length(l) !))                                      🝖-end-}
{- TODO: Proof of above
length(concatMap (insertedEverywhere x) (permutations(y ⊰ l)))
foldᵣ((_+_) ∘ length ∘ (insertedEverywhere x)) (permutations(y ⊰ l))
foldᵣ((_+_) ∘ 𝐒 ∘ length) (permutations(y ⊰ l))
foldᵣ((_+_) ∘ 𝐒) (map length(permutations(y ⊰ l)))
foldᵣ((_+_) ∘ 𝐒) (map (const(length(y ⊰ l))) (permutations(y ⊰ l))) -- from permutation-length when map function yields the same value for every element in the list
foldᵣ((_+_) ∘ 𝐒 ∘ const(length(y ⊰ l))) (permutations(y ⊰ l))
foldᵣ((_+_) ∘ const(𝐒 ∘ length(y ⊰ l))) (permutations(y ⊰ l))
𝐒(length(y ⊰ l)) ⋅ length(permutations(y ⊰ l))
𝐒(length(y ⊰ l)) ⋅ (length(y ⊰ l) !)
-}

{-  length(permutations (x ⊰ y ⊰ l))                                    🝖[ _≡_ ]-[ {!!} ]
  -- length(concatMap (insertedEverywhere x) (permutations(y ⊰ l)))      🝖[ _≡_ ]-[ length-concatMap {l = permutations(y ⊰ l)}{f = insertedEverywhere x} ]
  -- foldᵣ (_+_ ∘ length ∘ insertedEverywhere x) 𝟎 (permutations(y ⊰ l)) 🝖[ _≡_ ]-[ {!length-foldᵣ {l = permutations(y ⊰ l)}{init = 𝟎}!} ]
  𝐒(𝐒(length l)) ⋅ (𝐒(length l) ⋅ (length(l) !))                      🝖[ _≡_ ]-[]
  (length(x ⊰ y ⊰ l) !)                                               🝖-end
-}
