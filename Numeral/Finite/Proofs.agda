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
open import Numeral.Natural as ℕ hiding (𝐏)
open import Numeral.Natural.Function
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Proofs
import      Numeral.Natural.Relation as ℕ
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator
open import Syntax.Number
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs
open import Type.Properties.Empty
open import Type.Properties.Singleton

private variable ℓ : Lvl.Level
private variable N b₁ b₂ : ℕ

instance
  𝕟0-empty : IsEmpty{ℓ}(𝕟(0))
  IsEmpty.empty 𝕟0-empty ()

instance
  𝕟1-unit : IsUnit(𝕟(1))
  IsUnit.unit       𝕟1-unit = 𝟎
  IsUnit.uniqueness 𝕟1-unit {𝟎} = [≡]-intro

toℕ-bounded : ∀{N : ℕ}{n : 𝕟(N)} → (toℕ (n) < N)
toℕ-bounded{𝟎}   {()}
toℕ-bounded{𝐒 N}{𝟎}   = succ(_≤_.min)
toℕ-bounded{𝐒 N}{𝐒 n} = succ(toℕ-bounded{N}{n})

fromℕ-eq : ∀{M N n} ⦃ nM : IsTrue(n ℕ.<? M) ⦄ ⦃ nN : IsTrue(n ℕ.<? N) ⦄ → (fromℕ n {M} 𝕟.≡ fromℕ n {N})
fromℕ-eq {𝐒 M} {𝐒 N} {𝟎}   = [⊤]-intro
fromℕ-eq {𝐒 M} {𝐒 N} {𝐒 n} = fromℕ-eq {M} {N} {n}

toℕ-preserve-eq : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≡ n) → (toℕ m ≡ toℕ n)
toℕ-preserve-eq {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≡]-intro
toℕ-preserve-eq {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n}           = congruence₁(𝐒) ∘ toℕ-preserve-eq {M} {N} {m} {n}

toℕ-preserve-gt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.> n) → (toℕ m > toℕ n)
toℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
toℕ-preserve-gt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ toℕ-preserve-gt {M} {N} {m} {n} x ⦄

toℕ-preserve-lt : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.< n) → (toℕ m < toℕ n)
toℕ-preserve-lt {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-with-[𝐒] ⦃ [≤]-minimum ⦄
toℕ-preserve-lt {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ toℕ-preserve-lt {M} {N} {m} {n} x ⦄

toℕ-preserve-ge : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≥ n) → (toℕ m ≥ toℕ n)
toℕ-preserve-ge {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
toℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 n} {𝟎}   [⊤]-intro = [≤]-minimum
toℕ-preserve-ge {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ toℕ-preserve-ge {M} {N} {m} {n} x ⦄

toℕ-preserve-le : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≤ n) → (toℕ m ≤ toℕ n)
toℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝟎}   [⊤]-intro = [≤]-minimum
toℕ-preserve-le {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} [⊤]-intro = [≤]-minimum
toℕ-preserve-le {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x         = [≤]-with-[𝐒] ⦃ toℕ-preserve-le {M} {N} {m} {n} x ⦄

toℕ-preserve-ne : ∀{M N}{m : 𝕟(M)}{n : 𝕟(N)} → (m 𝕟.≢ n) → (toℕ m ≢ toℕ n)
toℕ-preserve-ne {𝐒 M} {𝐒 N} {𝟎}   {𝐒 n} _ ()
toℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝟎}   _ ()
toℕ-preserve-ne {𝐒 M} {𝐒 N} {𝐒 m} {𝐒 n} x p = toℕ-preserve-ne {M} {N} {m} {n} x (injective(𝐒) p)

congruence-fromℕ : ∀ ⦃ pos : ℕ.Positive(N) ⦄ {x} ⦃ px : IsTrue(x ℕ.<? N) ⦄ {y} ⦃ py : IsTrue(y ℕ.<? N) ⦄ → (x ≡ y) → (fromℕ x {N} ⦃ px ⦄ ≡ fromℕ y ⦃ py ⦄)
congruence-fromℕ [≡]-intro = [≡]-intro

fromℕ-function-raw : ∀{M N} ⦃ pos : ℕ.Positive(M) ⦄ {x} ⦃ px : IsTrue(x ℕ.<? M) ⦄ {y} ⦃ py : IsTrue(y ℕ.<? N) ⦄ → (x ≡ y) → (fromℕ x {M} 𝕟.≡ fromℕ y {N})
fromℕ-function-raw {𝐒 M}     {𝐒 N}     {x = 𝟎}   {y = 𝟎}   xy = <>
fromℕ-function-raw {𝐒 (𝐒 M)} {𝐒 (𝐒 N)} {x = 𝐒 x} {y = 𝐒 y} xy = fromℕ-function-raw {𝐒 M}{𝐒 N} {x = x}{y = y} (injective(𝐒) xy)

𝕟-ℕ-inverse : ∀{N n} ⦃ nN : IsTrue(n ℕ.<? N) ⦄ → (toℕ {n = N}(fromℕ n) ≡ n)
𝕟-ℕ-inverse {𝐒 N}{𝟎}   = [≡]-intro
𝕟-ℕ-inverse {𝐒 N}{𝐒 n} = congruence₁(𝐒) (𝕟-ℕ-inverse {N}{n})

ℕ-𝕟-inverse : ∀{N}{n : 𝕟(𝐒(N))} → (fromℕ(toℕ n) ⦃ toℕ-bound{n = n} ⦄ ≡ n)
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

maximum-function : ⦃ pos-b₁ : ℕ.Positive(b₁) ⦄ → ⦃ pos-b₂ : ℕ.Positive(b₂) ⦄ → (b₁ ≡ b₂) → (maximum{b₁} 𝕟.≡ maximum{b₂})
maximum-function {𝐒 𝟎} {.ℕ.𝟏}             [≡]-intro = <>
maximum-function {𝐒 (𝐒 b)} {.(𝐒 (𝐒 b))} [≡]-intro = maximum-function {𝐒 b} {𝐒 b} [≡]-intro

minimum-function : ⦃ pos-b₁ : ℕ.Positive(b₁) ⦄ → ⦃ pos-b₂ : ℕ.Positive(b₂) ⦄ → (minimum{b₁} 𝕟.≡ minimum{b₂})
minimum-function {𝐒 b₁} {𝐒 b₂} = <>
