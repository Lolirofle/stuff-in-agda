module Data.List.Relation.Permutation.ByInsertion.Oper where

import      Data
open import Data.List as List hiding (elim ; prepend)
open import Data.List.Functions as List using (length ; insertIn)
open import Data.List.Relation.Permutation.ByInsertion
import      Lvl
open import Numeral.Finite
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ l₃ l₄ : List(T)
private variable x y z : T

prepend : (l₁ permutes l₂) → ((x ⊰ l₁) permutes (x ⊰ l₂))
prepend p = ins 𝟎 p

refl : l permutes l
refl {l = ∅} = empty
refl {l = x ⊰ l} = prepend refl

swap : (x ⊰ y ⊰ l) permutes (y ⊰ x ⊰ l)
swap = ins 𝟏 (prepend refl)

flippedIns : (n : 𝕟₌(length l₂)) → (l₁ permutes l₂) → ((x ⊰ l₁) permutes (insertIn x l₂ n))
flippedIns 𝟎     empty     = refl
flippedIns 𝟎     (ins k p) = prepend (ins k p)
flippedIns (𝐒 n) (ins k p) = ins(𝐒 k) (flippedIns n p)

sym : (l₁ permutes l₂) → (l₂ permutes l₁)
sym empty = empty
sym (ins n p) = flippedIns n (sym p)

open import BidirectionalFunction using (_↔_ ; intro ; _$ₗ_ ; _$ᵣ_)
open import Data.List.Equiv.Id
open import Data.List.Functions.Proofs.Positional
open import Data.List.Proofs.Length
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Finite.Bound
open import Numeral.Finite.Bound.Proofs
open import Numeral.Finite.Bound.Substitution as 𝕟 using (𝕟-relator)
import      Numeral.Finite.Oper.Bounded as Bounded
open import Numeral.Finite.Oper.Bounded.Proofs.𝐒
open import Numeral.Finite.Relation.Order.Proofs
open import Numeral.Natural
import      Numeral.Natural.Relation.Order as ℕ
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator
open import Structure.Relator.Properties

ins2 : ∀{n₁ n₂} → (l₁ permutes l₂) → ((insertIn x l₁ n₁) permutes (insertIn x l₂ n₂))
ins2 {n₁ = 𝟎}    {𝟎}              = prepend
ins2 {n₁ = 𝟎}    {𝐒 n₂} (ins n p) = ins(𝐒(n)) (flippedIns n₂ p)
ins2 {n₁ = 𝐒 n₁} {𝟎}    (ins n p) = ins (𝐒(n₁)) (ins n p)
ins2 {x = x} {n₁ = 𝐒 n₁} {𝐒 n₂} (ins {l₁}{l₂} {x = y} n p) = [∨]-elim
  (\ord →
    let
      𝐒n₁ = Bounded.𝐒(n₁)
      𝐒n = 𝐒(substitute₁ₗ(𝕟) ⦃ 𝕟-relator ⦄ (length-insertIn{x = x} {l = l₁} {n = 𝐒n₁}) n)
      sw : (insertIn y (insertIn x l₁ 𝐒n₁) (𝐒n) ≡ insertIn x (insertIn y l₁ n) (𝐒 n₁))
      sw = insertIn-swapₗ'{n₁ = 𝐒n₁}{n₂ = 𝐒n}{n₃ = n}{n₄ = 𝐒 n₁}
         ([∨]-introₗ ([∨]-introᵣ ([↔]-to-[→] ([<][≤]-convert {a = n₁}{b = n}) ord)))
         ([↔]-to-[→] (bounded-𝐒-is-𝐒{bound(n₁)}{𝐒(length l₁)}{n₁}) ([<][≤]-subtransitivityᵣ-raw {a = n₁}{b = n}{c = maximum} ord ([≤]-maximum {a = n} (reflexivity(ℕ._≤_)))))
         (𝕟.subst-identity{eq = symmetry(_≡_) (length-insertIn{l = l₁}{n = 𝐒n₁})} {n = n})
    in substitute₂-₁ᵣ(_permutes_)(_) sw (ins{x = y} 𝐒n (ins2{x = x}{n₁ = 𝐒n₁}{n₂ = n₂} p)))
  (\ord →
    let
      n₁' = substitute₁ᵣ(𝕟) ⦃ 𝕟-relator ⦄ (length-insertIn {l = l₁} {n = n}) n₁
      n'  = substitute₁ₗ(𝕟) ⦃ 𝕟-relator ⦄ (length-insertIn {l = l₁} {n = n₁'}) n
      sw : (insertIn y (insertIn x l₁ n₁') (bound-𝐒 n') ≡ insertIn x (insertIn y l₁ n) (𝐒 n₁))
      sw = insertIn-swapᵣ{n₁ = n₁'}{n₂ = bound-𝐒(n')}{n₃ = n}{n₄ = 𝐒(n₁)}
         ([≥][≡]-subtransitivityₗ-raw {a = 𝕟.subst (length-insertIn{l = l₁}{n = n}) $ᵣ n₁}{b = n₁}{c = n} (𝕟.subst-identity{eq = length-insertIn{l = l₁}{n = n}}) ord)
         (𝕟.subst-identity {n = n₁})
         ([≡]-transitivity-raw {a = bound-𝐒(n')}{b = n'}{c = n}
           (bound-𝐒-identity{n = n'})
           (𝕟.subst-identity{_}{length(insertIn x l₁ n₁')}{n = n})
         )
    in substitute₂-₁ᵣ(_permutes_)(_) sw (ins{x = y} (bound-𝐒(n')) (ins2{x = x}{n₁ = n₁'}{n₂ = n₂} p))
  )
  ([<]-or-[≥] {a = n₁}{b = n})

transSym : (l₁ permutes l₂) → (l₃ permutes l₂)  → (l₁ permutes l₃)
transSym empty       empty        = empty
transSym (ins n p12) (ins n₁ p23) = ins2(transSym p12 p23)

trans : (l₁ permutes l₂) → (l₂ permutes l₃)  → (l₁ permutes l₃)
trans p q = transSym p (sym q)
