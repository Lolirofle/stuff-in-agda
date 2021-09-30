module Data.List.Relation.Permutation.ByInsertion where

import      Data
open import Data.Boolean
open import Data.List
open import Data.List.Functions renaming (module LongOper to List)
open import Data.List.Relation
open import Data.List.Relation.Permutation
open import Functional using (id ; _∘_ ; const)
open import Logic.Propositional
open import Logic
import      Lvl
open import Numeral.Finite
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ l₃ l₄ : List(T)
private variable x y z : T
private variable f : A → B
private variable P : T → Bool

open import Data.List.Proofs
open import Data.List.Equiv.Id
open import Lang.Inspect
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Finite.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
import      Structure.Function.Names as Names
open import Structure.Function.Proofs
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid using (Equiv)
open import Syntax.Function
open import Syntax.Transitivity

module InsertionPermutation where
data _insertion-permutes_ {ℓ} {T : Type{ℓ}} : List(T) → List(T) → Stmt{Lvl.𝐒(ℓ)} where
  empty : ∅ insertion-permutes ∅
  ins : (n : 𝕟₌(length l₁)) → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n) insertion-permutes (x ⊰ l₂))

open import Data.List.Proofs.Length
open import Relator.Equals.Proofs
open import Structure.Relator

insertion-permutation-mapping : (l₁ insertion-permutes l₂) → (𝕟(length(l₁)) → 𝕟(length(l₂)))
insertion-permutation-mapping empty                       ()
insertion-permutation-mapping (ins 𝟎 p)                   𝟎     = 𝟎
insertion-permutation-mapping (ins {l₁ = x ⊰ l₁} (𝐒 n) p) 𝟎     = 𝟎
insertion-permutation-mapping (ins 𝟎 p)                   (𝐒 i) = 𝐒(insertion-permutation-mapping p i)
insertion-permutation-mapping (ins {l₁ = x ⊰ l₁} (𝐒 n) p) (𝐒 i) = 𝐒(insertion-permutation-mapping p (substitute₁(𝕟) (length-insertIn {l = l₁} {n = n}) i))

open import Data using ()
open import Numeral.Natural
open import Relator.Equals
open import Syntax.Number

{-insertion-permutes-prop : (perm₁ perm₂ : l₁ insertion-permutes l₂) → (perm₁ ≡ perm₂)
insertion-permutes-prop = insertion-permutes-elim(\{l₁}{l₂} perm₁ → (perm₂ : l₁ insertion-permutes l₂) → (perm₁ ≡ perm₂))
  (\{empty → [≡]-intro})
  \{l₁}{l₂}{x}{n} perm₁ prev → {!insertion-permutes-elim(\{l₁}{l₂} perm₂ → ∀{n} → (perm₁ : l₁ insertion-permutes l₂) → (perm₁ ≡ perm₂)) ? ?!}-}
{-insertion-permutes-prop {l₁ = ∅} {∅} empty empty = {!!}
insertion-permutes-prop {l₁ = ∅} {x ⊰ l₂} perm₁ perm₂ = {!perm₁ perm₂!}
insertion-permutes-prop {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} perm₁ perm₂ = {!perm₁ perm₂!}-}

insertion-permutes-prepend : (l₁ insertion-permutes l₂) → ((x ⊰ l₁) insertion-permutes (x ⊰ l₂))
insertion-permutes-prepend p = ins 𝟎 p

insertion-permutes-refl : l insertion-permutes l
insertion-permutes-refl {l = ∅} = empty
insertion-permutes-refl {l = x ⊰ l} = insertion-permutes-prepend insertion-permutes-refl

insertion-permutes-swap : (x ⊰ y ⊰ l) insertion-permutes (y ⊰ x ⊰ l)
insertion-permutes-swap = ins 1 (insertion-permutes-prepend insertion-permutes-refl)

{-
insertion-permutes-to-permutes : (l₁ insertion-permutes l₂) → (l₁ permutes l₂)
insertion-permutes-to-permutes empty     = empty
insertion-permutes-to-permutes (ins n p) = trans permutes-insertIn (prepend (insertion-permutes-to-permutes p))
-}

insertion-permutes-flipped-ins : ∀{n} → (l₁ insertion-permutes l₂) → ((x ⊰  l₁) insertion-permutes (insertIn x l₂ n))
insertion-permutes-flipped-ins {n = 𝟎}   empty      = insertion-permutes-refl
insertion-permutes-flipped-ins {n = 𝟎}   (ins k p)  = insertion-permutes-prepend (ins k p)
insertion-permutes-flipped-ins {n = 𝐒 n} (ins k p) = ins (𝐒 k) (insertion-permutes-flipped-ins {n = n} p)

insertion-permutes-sym : (l₁ insertion-permutes l₂) → (l₂ insertion-permutes l₁)
insertion-permutes-sym empty = empty
insertion-permutes-sym (ins n p) = insertion-permutes-flipped-ins(insertion-permutes-sym p)

open import Structure.Function
open import Syntax.Transitivity

insertion-permutes-length : (l₁ insertion-permutes l₂) → (length l₁ ≡ length l₂)
insertion-permutes-length empty                         = [≡]-intro
insertion-permutes-length (ins {l₁ = l₁}{x = x} n perm) = length-insertIn{x = x}{l₁}{n} 🝖 congruence₁(𝐒) (insertion-permutes-length perm)

insertion-permutes-elim : ∀{ℓ}(P : ∀{l₁ l₂ : List(T)} → (l₁ insertion-permutes l₂) → Type{ℓ}) → P(empty) → (∀{l₁ l₂}{x}{n}(perm : l₁ insertion-permutes l₂) → P(perm) → P(ins{x = x} n perm)) → (∀{l₁ l₂}(perm : l₁ insertion-permutes l₂) → P(perm))
insertion-permutes-elim P pe ps empty = pe
insertion-permutes-elim P pe ps (ins n perm) = ps perm (insertion-permutes-elim P pe ps perm)

open import Structure.Relator.Properties
module ProofHeight where
  height : (l₁ insertion-permutes l₂) → ℕ
  height empty        = 𝟎
  height (ins _ perm) = 𝐒(height perm)

  height-is-lengthᵣ : ∀{perm : l₁ insertion-permutes l₂} → (height perm ≡ length l₂)
  height-is-lengthᵣ {l₁ = _} {l₂ = _} {perm = empty}             = [≡]-intro
  height-is-lengthᵣ {l₁ = l₁}{l₂ = l₂}{perm = ins{x = x} n perm} = congruence₁(𝐒) (height-is-lengthᵣ{perm = perm})

  height-is-lengthₗ : ∀{perm : l₁ insertion-permutes l₂} → (height perm ≡ length l₁)
  height-is-lengthₗ {perm = perm} = height-is-lengthᵣ 🝖 symmetry(_≡_) (insertion-permutes-length perm)

  open import Data.Tuple
  open import Logic.Predicate
  open import Numeral.Natural.Relation
  height-step : ∀{perm : l₁ insertion-permutes l₂} → Positive(height perm) → ∃{Obj = T ⨯ List(T) ⨯ List(T)}(\{(x , l1 , l2) → ∃(n ↦ (l₁ ≡ insertIn x l1 n) ∧ (l₂ ≡ x ⊰ l2) ∧ ∃{Obj = l1 insertion-permutes l2}(p ↦ height perm ≡ 𝐒(height(p))))})
  height-step {perm = ins {l₁ = l₁} {l₂ = l₂} {x} n perm} pos = [∃]-intro (x , l₁ , l₂) ⦃ [∃]-intro n ⦃ [∧]-intro ([∧]-intro [≡]-intro [≡]-intro) ([∃]-intro perm ⦃ [≡]-intro ⦄) ⦄ ⦄

  {-
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  insertion-permutes-strong-elim : ∀{ℓ}(P : ∀{l₁ l₂ : List(T)} → (l₁ insertion-permutes l₂) → Type{ℓ}) → (∀{l₁ l₂ l₃ l₄}(perm₁ : l₁ insertion-permutes l₂)(perm₂ : l₃ insertion-permutes l₄) → (height perm₁ < height perm₂) → P(perm₁) → P(perm₂)) → (∀{l₁ l₂}(perm : l₁ insertion-permutes l₂) → P(perm))
  insertion-permutes-strong-elim P step perm = insertion-permutes-elim(\{l₃}{l₄} perm₂ → ∀{l₁ l₂}(perm₁ : l₁ insertion-permutes l₂) → (height perm₁ < height perm₂) → P(perm₂))
    (\_ ())
    (\{ {l₃}{l₄}{x}{n} perm₂ prev {l₁}{l₂} perm₁ (succ ph) → step {!!} {!!} {!!} {!!} })
    (ins{x = {!!}} 𝟎 perm)
    perm
    {!(reflexivity(_≤_))!}
  -}

{-
-- open import Numeral.Finite.Relation.Order using (_≤_)
open import Numeral.Natural.Relation.Order
open import Structure.Operator
test : ∀{n₁ n₂} → (n₁ ≤ n₂) → (n₁ ≤ length(l)) → (n₂ ≤ length(l)) → (insert n₁ x (insert n₂ y l) ≡ insert (𝐒(n₂)) y (insert n₁ x l))
test {l = _}     min      min       _         = [≡]-intro
test {l = x ⊰ l} (succ p) (succ l1) (succ l2) = congruence₂ᵣ(_⊰_)(x) (test p l1 l2)

test2 : ∀{n₁ n₂} → (n₁ > n₂) → (n₁ ≤ length(l)) → (n₂ ≤ length(l)) → (insert (𝐒(n₁)) x (insert n₂ y l) ≡ insert n₂ y (insert n₁ x l))
test2 {l = x ⊰ l} (succ p) (succ l1) min = [≡]-intro
test2 {l = x ⊰ l} (succ p) (succ l1) (succ l2) = congruence₂ᵣ(_⊰_)(x) (test2 p l1 l2)

insertIn-insert-eq : ∀{n} → (insertIn x l n ≡ insert (𝕟-to-ℕ n) x l)
insertIn-insert-eq {l = _}     {n = 𝟎}   = [≡]-intro
insertIn-insert-eq {l = x ⊰ l} {n = 𝐒 n} = congruence₂ᵣ(_⊰_)(x) (insertIn-insert-eq {l = l} {n = n})

ins1 : ∀{n₁ n₂} → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂)) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ (𝐒(n₂))))
ins1 = ?

ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))
ins2 {l₂ = ∅} empty = {!!}
ins2 {l₂ = x ⊰ l₂} {n₁ = n₁} {n₂ = 𝟎} p = ins n₁ p
ins2 {l₁ = ∅} {l₂ = x ⊰ l₂} {n₁ = n₁} {n₂ = 𝐒 n₂} p = {!!}
ins2 {l₁ = x₁ ⊰ l₁} {l₂ = x₂ ⊰ l₂}{x = x} {n₁ = n₁} {n₂ = 𝐒 n₂} p = {!ins2{l₁ = l₁}{l₂ = l₂}{x = x}{n₂ = n₂} !}
{-ins2{n₁ = 𝟎} {n₂ = 𝟎} p = {!!}
ins2{n₁ = 𝟎} {n₂ = 𝐒 n₂} p = {!!}
ins2{n₁ = 𝐒 n₁} {n₂ = 𝟎} p = {!!}
ins2{n₁ = 𝐒 n₁} {n₂ = 𝐒 n₂} (ins 𝟎 p) = {!!}
ins2{n₁ = 𝐒 n₁} {n₂ = 𝐒 n₂} (ins (𝐒 n) p) = {!ins ? (ins2 {n₂ = n₂} p)!}-} -- where
  -- pp : (insertIn x (insertIn y l₁ (𝐒 n₁)) n₂ insertion-permutes l₂) → (insertIn y (insertIn x l₁ n₂) (𝐒 n₁) insertion-permutes l₂)

insertion-permutes-trans : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
insertion-permutes-trans empty            empty            = empty
insertion-permutes-trans (ins 𝟎 l12)      (ins 𝟎 l32)      = insertion-permutes-prepend (insertion-permutes-trans l12 l32)
insertion-permutes-trans (ins 𝟎 l12)      (ins (𝐒 n₂) l32) = insertion-permutes-flipped-ins {n = 𝐒 n₂} (insertion-permutes-trans l12 l32)
insertion-permutes-trans (ins (𝐒 n₁) l12) (ins 𝟎 l32)      = ins (𝐒 n₁) (insertion-permutes-trans l12 l32)
insertion-permutes-trans (ins (𝐒 n₁) l12) (ins (𝐒 n₂) l32) = p(ins (𝐒 n₁) (insertion-permutes-trans l12 l32)) where
  p : ∀{n} → (l₁ insertion-permutes (x ⊰ l₂)) → (l₁ insertion-permutes (insertIn x l₂ n))
  p {l₂ = l₂} {n = 𝟎} (ins n₁ perm) = ins n₁ perm
  p {l₂ = x ⊰ l₂} {n = 𝐒 n} (ins 𝟎 perm) = {!!}
  p {l₂ = x ⊰ l₂} {n = 𝐒 n} (ins (𝐒 n₁) perm) = {!insertion-permutes-swap(ins ? perm)!}

  p2 : ∀{n} → ((x ⊰ l₁) insertion-permutes l₂) → ((insertIn x l₁ n) insertion-permutes l₂)
  p2 perm = {!perm!}
-}

{-
ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))

ins2 {l₁ = l₁} {l₂} {n₁ = n₁} {𝟎} p = ins n₁ p
ins2 {l₁ = .(insertIn x _ n)} {x ⊰ l₂} {n₁ = 𝟎} {𝐒 n₂} (ins n p) = insertion-permutes-trans (insertion-permutes-prepend (ins n p)) (ins(𝐒 n₂) insertion-permutes-refl)
ins2 {l₁ = .(insertIn x _ n)} {x ⊰ l₂} {n₁ = 𝐒 n₁} {𝐒 n₂} (ins n p) = {!!}

insertion-permutes-trans empty     empty     = empty
insertion-permutes-trans (ins m p) (ins n q) = {!!}
-- ins2(insertion-permutes-trans p q)
-}

{-
insertion-permutation-mapping-correctness : (p : (l₁ insertion-permutes l₂)) → Proofs.PermutationMappingCorrectness l₁ l₂ (insertion-permutation-mapping p)
insertion-permutation-mapping-correctness (ins {l₁ = ∅} 𝟎 p) {𝟎} = [≡]-intro
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝟎} = [≡]-intro
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝐒 i} = insertion-permutation-mapping-correctness p
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝟎} = {!!}
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝐒 i} = {!!}
-}

-- test : (p : (l₁ insertion-permutes l₂)) → (∀{i} → (index l₁(insertion-permutation-mapping p i) ≡ index l₂(i)))
-- test p = ?

{-
open import Data.Boolean.Stmt
open import Numeral.Finite.Oper.Comparisons
test : ∀{l : List(T)}{n₁ : 𝕟(𝐒(length l))}{n₂ : 𝕟(𝐒(length (insertIn y l n₁)))} → IsTrue(n₁ >? n₂) → (insertIn y (insertIn x l n₁) n₂ ≡ insertIn x (insertIn y l n₁) n₂)
test p = {!!}
-}

{-
ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))
ins2 {n₁ = 𝟎} {𝟎} empty = insertion-permutes-refl
ins2 {n₁ = n₁} {𝟎} (ins n p) = ins n₁ (ins n p)
ins2 {x = x} {n₁ = n₁} {𝐒 n₂} (ins {x = y} n p) = {!(ins2 {x = x}{n₁ = n}{n₂ = n₂} p)!}

insertion-permutes-trans : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
insertion-permutes-trans empty empty = empty
insertion-permutes-trans (ins m p) (ins n q) = {!!}
-}

{-
test : ∀{n} → (l₁ insertion-permutes (y ⊰ insertIn x l₂ n)) → (l₁ insertion-permutes (x ⊰ insertIn y l₂ n))
test {l₂ = l₂} (ins {l₁ = l₁} n p) = {!!}

ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))
ins2 {n₁ = n₁} {𝟎} p = ins n₁ p
ins2 {n₁ = n₁} {𝐒 n₂} (ins {x = x} n p) = test(ins n₁ (ins2{x = x}{n}{n₂} p))

-- insertIn x₁ (insertIn x l₁ n) n₁
-- x ⊰ insertIn x₁ l₂ n₂

tr : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
tr {l₂ = ∅}       empty      empty      = empty
tr {l₂ = x₂ ⊰ l₂} (ins n₁ p) (ins n₂ q) = ins2(tr p q)

sym : (l₁ insertion-permutes l₂) → (l₂ insertion-permutes l₁)
sym = tr insertion-permutes-refl
-}
