module Numeral.Natural.Inductions{ℓ} where

import Lvl
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Induction{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Numeral.Natural.Relation.Order.Proofs{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

[ℕ]-unnecessary-induction : ∀{b : ℕ}{φ : ℕ → Stmt} → (∀(i : ℕ) → (i ≤ b) → φ(i)) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-unnecessary-induction {𝟎}   {φ} (base) (next) = [ℕ]-induction {φ} (base(𝟎) ([≤]-minimum)) (next)
[ℕ]-unnecessary-induction {𝐒(b)}{φ} (base) (next) = [ℕ]-unnecessary-induction {b}{φ} (base-prev) (next) where
  base-prev : ∀(i : ℕ) → (i ≤ b) → φ(i)
  base-prev(𝟎)    (proof) = base(𝟎) ([≤]-minimum)
  base-prev(𝐒(i)) (proof) = next(i) (base-prev(i) ([≤]-predecessor {i}{b} proof))

-- TODO: Can this proof be made more simple?
[ℕ]-strong-induction : ∀{φ : ℕ → Stmt} → φ(𝟎) → (∀{i : ℕ} → (∀{j : ℕ} → (j ≤ i) → φ(j)) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-strong-induction {φ} (base) (next) {n} = ([ℕ]-inductionᵢ {Q} (Q0) (QS) {n}) {n} (reflexivity) where
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
    qn{a} (a≤n) = qk{a} (transitivity{_}{_}{a} (a≤n) (n≤k))
