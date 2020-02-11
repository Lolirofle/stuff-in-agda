module Numeral.Finite.Proofs where

import Lvl
open import Data.Boolean.Stmt
open import Functional
open import Syntax.Number
open import Logic.Computability.Binary
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
import      Numeral.Finite.Oper.Comparisons as 𝕟
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Computability
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain

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

𝕟-ℕ-inverse : ∀{N n} ⦃ nN : IsTrue(n <? N) ⦄ → (𝕟-to-ℕ {n = N}(ℕ-to-𝕟 n) ≡ n)
𝕟-ℕ-inverse {𝐒 N}{𝟎}   = [≡]-intro
𝕟-ℕ-inverse {𝐒 N}{𝐒 n} = [≡]-with(𝐒) (𝕟-ℕ-inverse {N}{n})

ℕ-𝕟-inverse : ∀{N}{n : 𝕟(𝐒(N))} → (ℕ-to-𝕟(𝕟-to-ℕ n) ⦃ [↔]-to-[→] (ComputablyDecidable.proof-istrue(_<_)) (bounded{N}{n}) ⦄ ≡ n)
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
