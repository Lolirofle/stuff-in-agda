module Numeral.Finite.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Finite
import      Numeral.Finite.Oper.Comparisons as 𝕟
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Syntax.Number
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

private variable N : ℕ

bounded : ∀{N : ℕ}{n : 𝕟(𝐒(N))} → (𝕟-to-ℕ(n) < 𝐒(N))
bounded{_}   {𝟎}    = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
bounded{𝐒(N)}{𝐒(n)} = [≤]-with-[𝐒] ⦃ bounded{N}{n} ⦄

ℕ-to-𝕟-eq : ∀{M N n} ⦃ nM : IsTrue(n <? M) ⦄ ⦃ nN : IsTrue(n <? N) ⦄ → IsTrue(ℕ-to-𝕟 n {n = M} ⦃ nM ⦄ 𝕟.≡? ℕ-to-𝕟 n {n = N} ⦃ nN ⦄)
ℕ-to-𝕟-eq {𝐒 M} {𝐒 N} {𝟎}   = [⊤]-intro
ℕ-to-𝕟-eq {𝐒 M} {𝐒 N} {𝐒 n} = ℕ-to-𝕟-eq {M} {N} {n}

𝕟-to-ℕ-preserve-eq : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.≡? n) → (𝕟-to-ℕ m ≡ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-eq {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≡]-intro
𝕟-to-ℕ-preserve-eq {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n}           = [≡]-with(𝐒) ∘ 𝕟-to-ℕ-preserve-eq {M} {N} {m} {n}

𝕟-to-ℕ-preserve-gt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.>? n) → (𝕟-to-ℕ m > 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
𝕟-to-ℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-gt {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-lt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.<? n) → (𝕟-to-ℕ m < 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-lt {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
𝕟-to-ℕ-preserve-lt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-lt {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-ge : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.≥? n) → (𝕟-to-ℕ m ≥ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 n} {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-ge {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-le : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.≤? n) → (𝕟-to-ℕ m ≤ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-le {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-ne : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → IsTrue(m 𝕟.≢? n) → (𝕟-to-ℕ m ≢ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} _ ()
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   _ ()
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x p = 𝕟-to-ℕ-preserve-ne {M} {N} {m} {n} x (injective(𝐒) p)

congruence-ℕ-to-𝕟 : ∀ ⦃ pos : IsTrue(positive? N) ⦄ {x} ⦃ px : IsTrue(x <? N) ⦄ {y} ⦃ py : IsTrue(y <? N) ⦄ → (x ≡ y) → (ℕ-to-𝕟 x {N} ⦃ px ⦄ ≡ ℕ-to-𝕟 y ⦃ py ⦄)
congruence-ℕ-to-𝕟 [≡]-intro = [≡]-intro

𝕟-ℕ-inverse : ∀{N n} ⦃ nN : IsTrue(n <? N) ⦄ → (𝕟-to-ℕ {n = N}(ℕ-to-𝕟 n) ≡ n)
𝕟-ℕ-inverse {𝐒 N}{𝟎}   = [≡]-intro
𝕟-ℕ-inverse {𝐒 N}{𝐒 n} = [≡]-with(𝐒) (𝕟-ℕ-inverse {N}{n})

ℕ-𝕟-inverse : ∀{N}{n : 𝕟(𝐒(N))} → (ℕ-to-𝕟(𝕟-to-ℕ n) ⦃ [↔]-to-[→] decider-true (bounded{n = n}) ⦄ ≡ n)
ℕ-𝕟-inverse {𝟎}   {𝟎}   = [≡]-intro
ℕ-𝕟-inverse {𝐒 N} {𝟎}   = [≡]-intro
ℕ-𝕟-inverse {𝐒 N} {𝐒 n} = [≡]-with(𝐒) (ℕ-𝕟-inverse{N}{n})

instance
  [<]-of-𝕟-to-ℕ : ∀{N : ℕ}{n : 𝕟(N)} → (𝕟-to-ℕ (n) < N)
  [<]-of-𝕟-to-ℕ {𝟎} {()}
  [<]-of-𝕟-to-ℕ {𝐒 N} {𝟎}   = [≤]-with-[𝐒]
  [<]-of-𝕟-to-ℕ {𝐒 N} {𝐒 n} = [≤]-with-[𝐒] ⦃ [<]-of-𝕟-to-ℕ {N} {n} ⦄

instance
  [𝐒]-injective : ∀{N : ℕ} → Injective(𝕟.𝐒{N})
  Injective.proof [𝐒]-injective [≡]-intro = [≡]-intro

[≡][≡?]-equivalence : ∀{n}{i j : 𝕟(n)} → (i ≡ j) ↔ IsTrue(i 𝕟.≡? j)
[≡][≡?]-equivalence {𝐒 n} {𝟎}   {𝟎}   = [↔]-intro (const [≡]-intro) (const [⊤]-intro)
[≡][≡?]-equivalence {𝐒 n} {𝟎}   {𝐒 j} = [↔]-intro (\()) (\())
[≡][≡?]-equivalence {𝐒 n} {𝐒 i} {𝟎}   = [↔]-intro (\()) (\())
[≡][≡?]-equivalence {𝐒 n} {𝐒 i} {𝐒 j} = [∧]-map ([≡]-with(𝐒) ∘_) (_∘ injective(𝐒)) ([≡][≡?]-equivalence {n} {i} {j})

instance
  [≡][𝕟]-decider : ∀{n} → Decider(2)(_≡_ {T = 𝕟(n)})(𝕟._≡?_)
  [≡][𝕟]-decider {𝐒 n} {𝟎}   {𝟎}   = true [≡]-intro
  [≡][𝕟]-decider {𝐒 n} {𝟎}   {𝐒 y} = false \()
  [≡][𝕟]-decider {𝐒 n} {𝐒 x} {𝟎}   = false \()
  [≡][𝕟]-decider {𝐒 n} {𝐒 x} {𝐒 y} = step{f = id} (true ∘ [≡]-with(𝐒)) (false ∘ contrapositiveᵣ(injective(𝐒))) ([≡][𝕟]-decider {n} {x} {y})

maximum-0 : (maximum{N} ≡ 𝟎) → (N ≡ 𝟎)
maximum-0 {𝟎} _ = [≡]-intro
