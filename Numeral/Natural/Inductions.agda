module Numeral.Natural.Inductions where

import Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Numeral.Natural
import      Numeral.Natural.Induction
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties
open import Type

module _ {ℓ} where
  open Numeral.Natural.Induction{ℓ}

  [ℕ]-unnecessary-induction : ∀{b : ℕ}{φ : ℕ → Stmt{ℓ}} → (∀(i : ℕ) → (i ≤ b) → φ(i)) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
  [ℕ]-unnecessary-induction {𝟎}   {φ} (base) (next) = [ℕ]-induction {φ} (base(𝟎) ([≤]-minimum)) (next)
  [ℕ]-unnecessary-induction {𝐒(b)}{φ} (base) (next) = [ℕ]-unnecessary-induction {b}{φ} (base-prev) (next) where
    base-prev : ∀(i : ℕ) → (i ≤ b) → φ(i)
    base-prev(𝟎)    (proof) = base(𝟎) ([≤]-minimum)
    base-prev(𝐒(i)) (proof) = next(i) (base-prev(i) ([≤]-predecessor {i}{b} proof))

  [ℕ]-multiple-base-cases-induction : ∀{b : ℕ}{φ : ℕ → Stmt{ℓ}} → (∀(i : ℕ) → (i ≤ b) → φ(i)) → (∀(i : ℕ) → (b ≤ i) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
  [ℕ]-multiple-base-cases-induction {𝟎}   {φ} base next = [ℕ]-induction {φ} (base(𝟎) ([≤]-minimum)) (i ↦ next(i) ([≤]-minimum))
  [ℕ]-multiple-base-cases-induction {𝐒(b)}{φ} base next = [ℕ]-multiple-base-cases-induction {b}{φ} (base-prev) (next-prev) where
    base-prev : ∀(i : ℕ) → (i ≤ b) → φ(i)
    base-prev(i) (proof) = base(i) ([≤]-successor proof)

    next-prev : ∀(i : ℕ) → (b ≤ i) → φ(i) → φ(𝐒(i))
    next-prev(i) (proof) (φi) with [≤]-to-[<][≡] proof
    ...                          | [∨]-introₗ a<b       = next(i) (a<b) φi
    ...                          | [∨]-introᵣ [≡]-intro = base(𝐒(b)) (reflexivity(_≤_))

  [ℕ]-strong-induction : ∀{φ : ℕ → Stmt{ℓ}} → φ(𝟎) → (∀{i : ℕ} → (∀{j : ℕ} → (j ≤ i) → φ(j)) → φ(𝐒(i))) → (∀{n} → φ(n))
  [ℕ]-strong-induction {φ} (base) (next) {n} = ([ℕ]-inductionᵢ {Q} (Q0) (QS) {n}) {n} (reflexivity(_≤_)) where
    Q : ℕ → Stmt
    Q(k) = (∀{n} → (n ≤ k) → φ(n))

    Q0 : Q(𝟎)
    Q0{𝟎}    (_) = base
    Q0{𝐒(j)} (proof) = [⊥]-elim([≤][0]ᵣ-negation {j} (proof))

    QS : ∀{k : ℕ} → Q(k) → Q(𝐒(k))
    QS{k} (qk) {𝟎}    (0≤Sk)  = base
    QS{k} (qk) {𝐒(n)} (Sn≤Sk) = (next{n} (qn)) :of: φ(𝐒(n)) where
      n≤k : n ≤ k
      n≤k = [≤]-without-[𝐒] {n}{k} (Sn≤Sk)

      qn : Q(n)
      qn{a} (a≤n) = qk{a} ((a≤n) 🝖 (n≤k))

  [ℕ]-multiple-base-cases-strong-induction : ∀{b : ℕ}{φ : ℕ → Stmt{ℓ}} → (∀{i : ℕ} → (i ≤ b) → φ(i)) → (∀{i : ℕ} → (b ≤ i) → (∀{j : ℕ} → (b ≤ j) → (j ≤ i) → φ(j)) → φ(𝐒(i))) → (∀{n} → φ(n))
  [ℕ]-multiple-base-cases-strong-induction {𝟎}    {φ} base next {n} = [ℕ]-strong-induction{φ} ((base [≤]-minimum)) (\{i} → φj ↦ next{i} [≤]-minimum (\{j} _ → φj{j}))
  [ℕ]-multiple-base-cases-strong-induction {𝐒(b)} {φ} base next {n} =  [ℕ]-multiple-base-cases-strong-induction {b} {φ} base-prev next-prev {n} where
    base-prev : {i : ℕ} → i ≤ b → φ i
    base-prev{i} ib = base{i} ([≤]-successor ib)

    next-prev : {i : ℕ} → b ≤ i → ({j : ℕ} → b ≤ j → j ≤ i → φ j) → φ (𝐒 i)
    next-prev{i} bi φj with [≤]-to-[<][≡] bi
    ...                   | [∨]-introₗ b<i      = next{i} (b<i) (\{j} → bj ↦ φj{j} ([≤]-predecessor bj))
    ...                   | [∨]-introᵣ [≡]-intro = base{𝐒(i)} (reflexivity(_≤_))

  [ℕ]-strong-induction-with-monus : ∀{φ : ℕ → Stmt{ℓ}} → φ(𝟎) → (∀{i : ℕ} → (∀{j : ℕ} → φ(i −₀ j)) → φ(𝐒(i))) → (∀{n} → φ(n))
  [ℕ]-strong-induction-with-monus {φ} (base) (next) {n} = [ℕ]-strong-induction {φ} (base) (next2) {n} where
    convert-assumption : ∀{i} → (∀{j} → (j ≤ i) → φ(j)) → (∀{j} → φ(i −₀ j))
    convert-assumption {i} assumption {j} = assumption{i −₀ j} ([−₀]-lesser {i}{j})

    next2 : ∀{i} → (∀{j} → (j ≤ i) → φ(j)) → φ(𝐒(i))
    next2{i} assumption = next{i} (\{j} → convert-assumption{i} assumption {j})

  -- TODO: This is just a generalisation of [ℕ]-strong-induction-with-monus. If a function (T → 𝕟(i)) is surjective for every i∊ℕ, then f could be used in the induction step
  -- [ℕ]-induction-with-surjection : ∀{φ : ℕ → Stmt}{ℓT}{T : Type{ℓT}}{f : ℕ → T → ℕ}{f⁻¹ : (i : ℕ) → (n : ℕ) → ⦃ _ : n ≤ i ⦄ → T}
  --                               → (∀{i n} → (proof : (n ≤ i)) → (f(i)(f⁻¹(i)(n) ⦃ proof ⦄) ≡ n))
  --                               → φ(𝟎)
  --                               → (∀{i : ℕ}
  --                                 → (∀{t : T} → (φ ∘ f(i))(t))
  --                                 → φ(𝐒(i))
  --                               )
  --                               → (∀{n} → φ(n))
  -- [ℕ]-induction-with-surjection {φ}{ℓT}{T}{f}{f⁻¹} surj base next {n} = [ℕ]-strong-induction {φ} (base) (next2) {n} where
  --   postulate convert-assumption : ∀{i} → (∀{j} → (j ≤ i) → φ(j)) → (∀{t} → φ(f(i)(t)))
  --   -- convert-assumption {i} assumption {j} = assumption{i −₀ j} ([−₀]-lesser {i}{j})
  -- 
  --   next2 : ∀{i} → (∀{j} → (j ≤ i) → φ(j)) → φ(𝐒(i))
  --   next2{i} assumption = next{i} (\{j} → convert-assumption{i} assumption {j})
