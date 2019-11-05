module Numeral.Natural.Relation.Order.Existence where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
import      Numeral.Natural.Relation.Order as [≤def]
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Ordering
open import Structure.Function.Domain
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity

_≤_ : ℕ → ℕ → Stmt
_≤_ a b = ∃{Obj = ℕ}(n ↦ a + n ≡ b)

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_) (_<_) public

[≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
[≤]-with-[𝐒] {a} {b} ([∃]-intro n ⦃ f ⦄) =
  [∃]-intro
    (n)
    ⦃
      ([+1]-commutativity {a} {n}) -- 𝐒(a)+n = a+𝐒(n)
      🝖 ([≡]-with(𝐒) f) -- 𝐒(a+n)=a+𝐒(n) = 𝐒(b)
    ⦄

[≤]-equivalence : ∀{x y} → (x ≤ y) ↔ (x [≤def].≤ y)
[≤]-equivalence{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x [≤def].≤ y)
  l{𝟎}   {y}    ([≤def].[≤]-minimum)      = [∃]-intro(y) ⦃ [≡]-intro ⦄
  l{𝐒(x)}{𝟎}    ()
  l{𝐒(x)}{𝐒(y)} ([≤def].[≤]-with-[𝐒] ⦃ proof ⦄) = [≤]-with-[𝐒] {x}{y} (l{x}{y} (proof))

  r : ∀{x y} → (x ≤ y) → (x [≤def].≤ y)
  r{𝟎}   {y}    ([∃]-intro(z) ⦃ 𝟎+z≡y   ⦄) = [≤def].[≤]-minimum
  r{𝐒(x)}{𝟎}    ([∃]-intro(z) ⦃ ⦄)
  r{𝐒(x)}{𝐒(y)} ([∃]-intro(z) ⦃ 𝐒x+z≡𝐒y ⦄) = [≤def].[≤]-with-[𝐒] ⦃ r{x}{y} ([∃]-intro(z) ⦃ injective(𝐒)(𝐒x+z≡𝐒y) ⦄ ) ⦄
