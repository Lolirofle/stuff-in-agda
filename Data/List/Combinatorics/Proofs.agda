module Data.List.Combinatorics.Proofs where

import      Lvl
open import Data
open import Data.List
open import Data.List.Combinatorics
open import Data.List.Functions hiding (skip) renaming (module LongOper to List)
open        Data.List.Functions.LongOper
open import Data.List.Relation.Permutation
open import Data.List.Relation.Permutation.Proofs
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Data.List.Relation.Sublist
open import Data.List.Relation.Sublist.Proofs
open import Data.List.Proofs
open import Data.List.Equiv.Id
open import Data.List.Proofs.Length
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
import      Data.Tuple.Raiseᵣ as Tuple₊
import      Data.Tuple.Raiseᵣ.Functions as Tuple₊
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Combinatorics
open import Numeral.Natural.Combinatorics.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable x : T
private variable n k : ℕ

-- sublists₊(l) contains non-empty sublists of l.
sublists₊-correctness : AllElements(_⊑ l) (sublists₊(l))
sublists₊-correctness {l = ∅} = ∅
sublists₊-correctness {l = x ⊰ l} with sublists₊(l) | sublists₊-correctness {l = l}
... | ∅       | _       = use [≡]-intro [⊑]-minimum ⊰ ∅
... | sx ⊰ sl | px ⊰ pl = use [≡]-intro [⊑]-minimum ⊰ skip px ⊰ use [≡]-intro px ⊰ p pl where
  p : ∀{x : T}{l}{sl} → AllElements(_⊑ l) sl → AllElements(_⊑ (x ⊰ l)) (concatMap(y ↦ y ⊰ (x ⊰ y) ⊰ ∅) sl)
  p {sl = ∅}     ∅            = ∅
  p {sl = _ ⊰ _} (sll ⊰ alsl) = (skip sll) ⊰ (use [≡]-intro sll) ⊰ (p alsl)

-- sublists₊(l) lists all non-empty sublists of l.
sublists₊-completeness : (l₁ ⊑ l₂) → (l₁ ≡ ∅) ∨ (l₁ ∈ sublists₊(l₂))
sublists₊-completeness _⊑_.empty = [∨]-introₗ [≡]-intro
sublists₊-completeness {l₁ = x ⊰ l₁}{l₂ = y ⊰ l₂} (use xy p) = [∨]-introᵣ $ [∨]-elim
  (l₁∅ ↦ (• congruence₂(_⊰_) xy l₁∅))
  (⊰_ ∘ [↔]-to-[←] ([∈]-concatMap {f = x ↦ x ⊰ (y ⊰ x) ⊰ ∅}{l = sublists₊ l₂}) ∘ (l₁l₂ ↦ [∃]-intro l₁ ⦃ [∧]-intro l₁l₂ (⊰ • congruence₂ₗ(_⊰_)(l₁) xy) ⦄))
  (sublists₊-completeness p)
sublists₊-completeness {l₁ = l₁}{l₂ = x ⊰ l₂}(skip p) = [∨]-elim2
  id
  (⊰_ ∘ [↔]-to-[←] ([∈]-concatMap {f = y ↦ y ⊰ (x ⊰ y) ⊰ ∅}{l = sublists₊ l₂}) ∘ (l₁l₂ ↦ [∃]-intro l₁ ⦃ [∧]-intro l₁l₂ (• reflexivity(_≡_)) ⦄))
  (sublists₊-completeness p)

-- sublists(l) contains sublists of l.
sublists-correctness : AllElements(_⊑ l) (sublists(l))
sublists-correctness = [⊑]-minimum ⊰ sublists₊-correctness

-- sublists(l) lists all sublists of l.
sublists-completeness : (l₁ ⊑ l₂) → (l₁ ∈ sublists(l₂))
sublists-completeness sub with sublists₊-completeness sub
... | [∨]-introₗ p = • p
... | [∨]-introᵣ p = ⊰ p

-- (insertedEverywhere x l) contains permutations of x inserted into l.
permutes-insertedEverywhere : AllElements(_permutes (x ⊰ l)) (insertedEverywhere x l)
permutes-insertedEverywhere {x = x} {∅}     = _permutes_.prepend _permutes_.empty ⊰ ∅
permutes-insertedEverywhere {x = x} {y ⊰ l} = reflexivity(_permutes_) ⊰ AllElements-mapᵣ(y List.⊰_) (p ↦ trans (_permutes_.prepend p) _permutes_.swap) (permutes-insertedEverywhere {x = x} {l})

{-
AllElements-insertedEverywhere-function : ∀{P : List(T) → Type{ℓ}} → (∀{l₁ l₂}{x} → (l₁ permutes l₂) → (P(x ⊰ l₁) → P(x ⊰ l₂))) → (∀{l₁ l₂} → (l₁ permutes l₂) → (P(l₁) → P(l₂))) → (∀{l₁ l₂ : List(T)} → (l₁ permutes l₂) → (AllElements P (insertedEverywhere x l₁) → AllElements P (insertedEverywhere x l₂)))
AllElements-insertedEverywhere-function _ pperm {l₁ = ∅}      {∅}       _permutes_.empty   p@(_ ⊰ _) = p
AllElements-insertedEverywhere-function t pperm {l₁ = x ⊰ l₁} {.x ⊰ l₂} (_permutes_.prepend perm) (p ⊰ pl) =
  pperm (_permutes_.prepend (_permutes_.prepend perm)) p ⊰
  {!AllElements-insertedEverywhere-function t pperm {l₁ = l₁} {l₂} perm!} -- TODO: Probably needs more assumptions
  -- AllElements-insertedEverywhere-function {l₁ = l₁} {l₂} pperm perm (AllElements-without-map {!!} {!!} pl)
  -- AllElements-map (x List.⊰_) (\{l} → {!!}) (AllElements-insertedEverywhere-function {l₁ = l₁} {l₂} pperm perm {!!})
AllElements-insertedEverywhere-function _ pperm {l₁ = x ⊰ .(x₁ ⊰ _)} {x₁ ⊰ .(x ⊰ _)} _permutes_.swap (p₁ ⊰ p₂ ⊰ pl) =
  pperm (trans _permutes_.swap (_permutes_.prepend _permutes_.swap)) p₂ ⊰
  pperm (trans (_permutes_.prepend _permutes_.swap) _permutes_.swap) p₁ ⊰
  {!!}
AllElements-insertedEverywhere-function t pperm (trans perm₁ perm₂) = AllElements-insertedEverywhere-function t pperm perm₂ ∘ AllElements-insertedEverywhere-function t pperm perm₁
-}

-- permutations(l) contains permutations of l.
permutations-correctness : AllElements(_permutes l) (permutations(l))
permutations-correctness {l = ∅}         = _permutes_.empty ⊰ ∅
permutations-correctness {l = x ⊰ ∅}     = _permutes_.prepend _permutes_.empty ⊰ ∅
permutations-correctness {l = x ⊰ y ⊰ l} = AllElements-concatMap(insertedEverywhere x) (perm ↦ AllElements-of-transitive-binary-relationₗ (_permutes_.prepend perm) permutes-insertedEverywhere) (permutations-correctness {l = y ⊰ l})

permutations-of-[⊰] : permutations (x ⊰ l) ≡ concatMap (insertedEverywhere x) (permutations l)
permutations-of-[⊰] {l = ∅}     = [≡]-intro
permutations-of-[⊰] {l = x ⊰ l} = [≡]-intro

open import Data.Option
insertedEverywhere-first : first(insertedEverywhere x l) ≡ Option.Some(x ⊰ l)
insertedEverywhere-first {l = ∅}     = [≡]-intro
insertedEverywhere-first {l = x ⊰ l} = [≡]-intro

{- -- TODO: Transitivity is a problem. Maybe prove that _permutes_ and _insertion-permutes_ are equivalent first, and then count insertion-permutes which is much closer to the usual counting proof
permutations-completeness : (l₁ permutes l₂) → (l₁ ∈ permutations(l₂))
permutations-completeness _permutes_.empty          = • [≡]-intro
permutations-completeness (_permutes_.prepend {l₁ = l₁} {l₂} {x} perm) =
  [∃]-intro l₁ ⦃ [∧]-intro (permutations-completeness perm) {!insertIn!} ⦄ ⇒
  ∃(y ↦ (y ∈ permutations l₂) ∧ ((x ⊰ l₁) ∈ insertedEverywhere x y)) ⇒-[ [↔]-to-[←] [∈]-concatMap ]
  ((x ⊰ l₁) ∈ concatMap (insertedEverywhere x) (permutations l₂))    ⇒-[ substitute₁ₗ((x ⊰ l₁) ∈_) ⦃ [∈]-relatorᵣ ⦄ (permutations-of-[⊰] {x = x}{l = l₂}) ]
  ((x ⊰ l₁) ∈ permutations (x ⊰ l₂))                                 ⇒-end
permutations-completeness _permutes_.swap           = {!!}
permutations-completeness (trans perm₁ perm₂)       = {!permutations-completeness perm₁!}
-}

-- The number of unique sublists excluding the empty list.
sublists₊-length : length(sublists₊ l) ≡ (2 ^ (length l)) −₀ 1
sublists₊-length {l = ∅} = [≡]-intro
sublists₊-length {l = x ⊰ l} =
  length(sublists₊ (x ⊰ l))                                                               🝖[ _≡_ ]-[]
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

-- The number of unique sublists.
sublists-length : length(sublists l) ≡ 2 ^ (length l)
sublists-length {l = l} =
  length(sublists l)      🝖[ _≡_ ]-[]
  length(∅ ⊰ sublists₊ l) 🝖[ _≡_ ]-[]
  𝐒(length(sublists₊ l))  🝖[ _≡_ ]-[ [≡]-with(𝐒) (sublists₊-length {l = l}) ]
  𝐒((2 ^ length(l)) −₀ 1) 🝖[ _≡_ ]-[ [↔]-to-[→] [−₀][𝐒]ₗ-equality ([^]ₗ-growing {2}{0}{length l} (\()) [≤]-minimum) ]-sym
  𝐒(2 ^ length(l)) −₀ 1   🝖[ _≡_ ]-[]
  2 ^ length(l)           🝖-end

-- The number of unique combinations is computed by 𝑐𝐶.
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
repeatableCombinations-length {1}      {l = x ⊰ l} = congruence₁(𝐒) (symmetry(_≡_) (𝑐𝐶-singleton-subsets{length l}))
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
rotations-length{l = l} = length-accumulateIterate₀{f = rotateₗ}{init = l}

insertedEverywhere-contents-length : AllElements(p ↦ length(p) ≡ 𝐒(length(l))) (insertedEverywhere x l)
insertedEverywhere-contents-length = AllElements-fn (Function.congruence ⦃ _ ⦄ permutes-length-function) permutes-insertedEverywhere

insertedEverywhere-length : length(insertedEverywhere x l) ≡ 𝐒(length(l))
insertedEverywhere-length {x = x} {∅}     = [≡]-intro
insertedEverywhere-length {x = x} {a ⊰ l} =
  length(insertedEverywhere x (a ⊰ l))                                  🝖[ _≡_ ]-[]
  length((x ⊰ a ⊰ l) ⊰ (map (List.prepend a) (insertedEverywhere x l))) 🝖[ _≡_ ]-[]
  𝐒(length(map (List.prepend a) (insertedEverywhere x l)))              🝖[ _≡_ ]-[ [≡]-with(𝐒) (length-map{f = List.prepend a}{x = insertedEverywhere x l}) ]
  𝐒(length(insertedEverywhere x l))                                     🝖[ _≡_ ]-[ [≡]-with(𝐒) (insertedEverywhere-length {x = x} {l}) ]
  𝐒(𝐒(length(l)))                                                       🝖[ _≡_ ]-[]
  𝐒(length(a ⊰ l))                                                      🝖-end

-- All permutations of a list are of the same length, and is also the same as the length of the list itself.
permutation-length : AllElements(p ↦ length p ≡ length l) (permutations l)
permutation-length{l = l} = AllElements-fn (Function.congruence ⦃ _ ⦄ permutes-length-function) (permutations-correctness{l = l})

-- TODO: Move
map-operator-raw-function : ∀{f g : A → B} → AllElements(x ↦ f(x) ≡ g(x))(l) → (map f(l) ≡ map g(l))
map-operator-raw-function ∅       = [≡]-intro
map-operator-raw-function (p ⊰ l) = congruence₂(_⊰_) p (map-operator-raw-function l)

permutations-length : length(permutations l) ≡ length(l) !
permutations-length {l = ∅}         = [≡]-intro
permutations-length {l = x ⊰ ∅}     = [≡]-intro
permutations-length {l = x ⊰ y ⊰ l} =
  length(permutations(x ⊰ y ⊰ l))                                     🝖[ _≡_ ]-[]
  length(concatMap(insertedEverywhere x) (permutations(y ⊰ l)))       🝖[ _≡_ ]-[ length-concatMap{l = permutations(y ⊰ l)}{f = insertedEverywhere x} ]
  foldᵣ(_+_ ∘ length ∘ insertedEverywhere x) 𝟎 (permutations(y ⊰ l))  🝖[ _≡_ ]-[ foldᵣ-operator-raw {l₁ = permutations(y ⊰ l)} (\{l}{y} → congruence₂ₗ(_+_)(y) (insertedEverywhere-length{l = l})) [≡]-intro [≡]-intro ]
  foldᵣ(_+_ ∘ 𝐒 ∘ length) 𝟎 (permutations(y ⊰ l))                     🝖[ _≡_ ]-[ foldᵣ-map-preserve {f = length}{l = permutations(y ⊰ l)} ]
  foldᵣ(_+_ ∘ 𝐒) 𝟎 (map length(permutations(y ⊰ l)))                  🝖[ _≡_ ]-[ congruence₁(foldᵣ(_+_ ∘ 𝐒) 𝟎) (map-operator-raw-function(permutation-length{l = y ⊰ l})) ]
  foldᵣ(_+_ ∘ 𝐒) 𝟎 (map (const(length(y ⊰ l))) (permutations(y ⊰ l))) 🝖[ _≡_ ]-[ foldᵣ-map-preserve {f = const(length(y ⊰ l))}{l = permutations(y ⊰ l)} ]-sym
  foldᵣ(_+_ ∘ 𝐒 ∘ const(length(y ⊰ l))) 𝟎 (permutations(y ⊰ l))       🝖[ _≡_ ]-[]
  foldᵣ(_+_ ∘ const(𝐒(length(y ⊰ l)))) 𝟎 (permutations(y ⊰ l))        🝖[ _≡_ ]-[]
  foldᵣ(const(𝐒(length(y ⊰ l)) +_)) 𝟎 (permutations(y ⊰ l))           🝖[ _≡_ ]-[ foldᵣ-constant-[+]ₗ {l = permutations(y ⊰ l)}{step = 𝐒(length(y ⊰ l))} ]
  length(permutations(y ⊰ l)) ⋅ 𝐒(length(y ⊰ l)) + 𝟎                  🝖[ _≡_ ]-[]
  length(permutations(y ⊰ l)) ⋅ 𝐒(length(y ⊰ l))                      🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(𝐒(length(y ⊰ l))) (permutations-length {l = y ⊰ l}) ]
  (length(y ⊰ l)!) ⋅ 𝐒(length(y ⊰ l))                                 🝖[ _≡_ ]-[ commutativity(_⋅_) {length(y ⊰ l)!}{𝐒(length(y ⊰ l))} ]
  𝐒(length(y ⊰ l)) ⋅ (length(y ⊰ l)!)                                 🝖[ _≡_ ]-[]
  length(x ⊰ y ⊰ l)!                                                  🝖-end

{-permutations-length {l = x ⊰ y ⊰ l} with permutations(y ⊰ l) | permutations-length {l = y ⊰ l}
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


open import Numeral.Finite
tuples-correctness : ∀{t : T Tuple₊.^ n} → (∀{i : 𝕟(n)} → ((Tuple₊.index i t) ∈ l)) → (t ∈ tuples n l)
tuples-correctness {n = 𝟎}             {t = <>} dom = • [≡]-intro
tuples-correctness {n = 𝐒 𝟎}           {t = t}  dom = dom{𝟎}
tuples-correctness {n = 𝐒(𝐒 n)}{l = l} {t = (x , t)} dom =
  [↔]-to-[←] ([∈]-concatMap ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ {f = \x → map(Tuple₊.prepend x) (tuples(𝐒(n)) l)}{x = x , t}{l = l})
  ([∃]-intro x ⦃ [∧]-intro
    (dom{𝟎})
    (
      [↔]-to-[→] ([∈]-map {f = Tuple₊.prepend{n = 𝐒 n} _}{x , t}{l = tuples(𝐒 n) l})
      ([∃]-intro t ⦃ [∧]-intro ([≡]-intro{ℓ = Lvl.of(Type.of l)}) (tuples-correctness {n = 𝐒 n}{l = l}{t = t} (\{i} → dom{𝐒 i})) ⦄)
    )
  ⦄)
-- 
