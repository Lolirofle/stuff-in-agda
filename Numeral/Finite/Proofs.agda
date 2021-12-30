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
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.Natural.Oper.Proofs
import      Numeral.Natural.Relation as ℕ
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Syntax.Number
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs
open import Type.Properties.Empty
open import Type.Properties.Singleton

private variable ℓ : Lvl.Level
private variable N : ℕ

instance
  𝕟0-empty : IsEmpty{ℓ}(𝕟(0))
  IsEmpty.empty 𝕟0-empty ()

instance
  𝕟1-unit : IsUnit(𝕟(1))
  IsUnit.unit       𝕟1-unit = 𝟎
  IsUnit.uniqueness 𝕟1-unit {𝟎} = [≡]-intro

𝕟-to-ℕ-bounded : ∀{N : ℕ}{n : 𝕟(N)} → (𝕟-to-ℕ (n) < N)
𝕟-to-ℕ-bounded{𝟎}   {()}
𝕟-to-ℕ-bounded{𝐒 N}{𝟎}   = succ(_≤_.min)
𝕟-to-ℕ-bounded{𝐒 N}{𝐒 n} = succ(𝕟-to-ℕ-bounded{N}{n})

ℕ-to-𝕟-eq : ∀{M N n} ⦃ nM : IsTrue(n ℕ.<? M) ⦄ ⦃ nN : IsTrue(n ℕ.<? N) ⦄ → IsTrue(ℕ-to-𝕟 n {n = M} ⦃ nM ⦄ 𝕟.≡? ℕ-to-𝕟 n {n = N} ⦃ nN ⦄)
ℕ-to-𝕟-eq {𝐒 M} {𝐒 N} {𝟎}   = [⊤]-intro
ℕ-to-𝕟-eq {𝐒 M} {𝐒 N} {𝐒 n} = ℕ-to-𝕟-eq {M} {N} {n}

𝕟-to-ℕ-preserve-eq : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≡ n) → (𝕟-to-ℕ m ≡ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-eq {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≡]-intro
𝕟-to-ℕ-preserve-eq {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n}           = congruence₁(𝐒) ∘ 𝕟-to-ℕ-preserve-eq {M} {N} {m} {n}

𝕟-to-ℕ-preserve-gt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.> n) → (𝕟-to-ℕ m > 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
𝕟-to-ℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-gt {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-lt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.< n) → (𝕟-to-ℕ m < 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-lt {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
𝕟-to-ℕ-preserve-lt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-lt {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-ge : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≥ n) → (𝕟-to-ℕ m ≥ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 n} {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-ge {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-le : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≤ n) → (𝕟-to-ℕ m ≤ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-minimum
𝕟-to-ℕ-preserve-le {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ 𝕟-to-ℕ-preserve-le {M} {N} {m} {n} x ⦄

𝕟-to-ℕ-preserve-ne : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≢ n) → (𝕟-to-ℕ m ≢ 𝕟-to-ℕ n)
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} _ ()
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   _ ()
𝕟-to-ℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x p = 𝕟-to-ℕ-preserve-ne {M} {N} {m} {n} x (injective(𝐒) p)

congruence-ℕ-to-𝕟 : ∀ ⦃ pos : ℕ.Positive(N) ⦄ {x} ⦃ px : IsTrue(x ℕ.<? N) ⦄ {y} ⦃ py : IsTrue(y ℕ.<? N) ⦄ → (x ≡ y) → (ℕ-to-𝕟 x {N} ⦃ px ⦄ ≡ ℕ-to-𝕟 y ⦃ py ⦄)
congruence-ℕ-to-𝕟 [≡]-intro = [≡]-intro

𝕟-ℕ-inverse : ∀{N n} ⦃ nN : IsTrue(n ℕ.<? N) ⦄ → (𝕟-to-ℕ {n = N}(ℕ-to-𝕟 n) ≡ n)
𝕟-ℕ-inverse {𝐒 N}{𝟎}   = [≡]-intro
𝕟-ℕ-inverse {𝐒 N}{𝐒 n} = congruence₁(𝐒) (𝕟-ℕ-inverse {N}{n})

ℕ-𝕟-inverse : ∀{N}{n : 𝕟(𝐒(N))} → (ℕ-to-𝕟(𝕟-to-ℕ n) ⦃ 𝕟-to-ℕ-bound{n = n} ⦄ ≡ n)
ℕ-𝕟-inverse {𝟎}   {𝟎}   = [≡]-intro
ℕ-𝕟-inverse {𝐒 N} {𝟎}   = [≡]-intro
ℕ-𝕟-inverse {𝐒 N} {𝐒 n} = congruence₁(𝐒) (ℕ-𝕟-inverse{N}{n})

instance
  [𝐒]-injective : ∀{N : ℕ} → Injective(𝕟.𝐒{N})
  Injective.proof [𝐒]-injective [≡]-intro = [≡]-intro

[≡][≡?]-equivalence : ∀{n}{i j : 𝕟(n)} → (i ≡ j) ↔ (i 𝕟.≡ j)
[≡][≡?]-equivalence {𝐒 n} {𝟎}  {𝟎}   = [↔]-intro (const [≡]-intro) (const [⊤]-intro)
[≡][≡?]-equivalence {𝐒 n} {𝟎}  {𝐒 _} = [↔]-intro (\()) (\())
[≡][≡?]-equivalence {𝐒 n} {𝐒 _}{𝟎}   = [↔]-intro (\()) (\())
[≡][≡?]-equivalence {𝐒 n} {𝐒 x}{𝐒 y} = [∧]-map (congruence₁(𝐒) ∘_) (_∘ injective(𝐒)) ([≡][≡?]-equivalence {n} {x}{y})

[≢][≢?]-equivalence : ∀{n}{i j : 𝕟(n)} → (i ≢ j) ↔ (i 𝕟.≢ j)
[≢][≢?]-equivalence = [↔]-intro l r where
  l : ∀{n}{i j : 𝕟(n)} → (i ≢ j) ← (i 𝕟.≢ j)
  l {𝐒 n}{𝐒 i}{𝐒 j} nij = l{n}{i}{j} nij ∘ injective(𝐒)
  l {𝐒 n}{𝐒 i}{𝟎}   nij ()

  r : ∀{n}{i j : 𝕟(n)} → (i ≢ j) → (i 𝕟.≢ j)
  r {𝐒 n} {𝟎} {𝟎}     = apply [≡]-intro
  r {𝐒 n} {𝟎} {𝐒 j}   = const <>
  r {𝐒 n} {𝐒 i} {𝟎}   = const <>
  r {𝐒 n} {𝐒 i} {𝐒 j} = r{n}{i}{j} ∘ (_∘ congruence₁(𝐒))

maximum-is-minimum-1 : ⦃ pos : ℕ.Positive(N) ⦄ → (maximum{N} ≡ minimum{N}) → (N ≡ 1)
maximum-is-minimum-1 {1} _ = [≡]-intro
