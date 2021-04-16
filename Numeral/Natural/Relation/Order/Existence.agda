module Numeral.Natural.Relation.Order.Existence where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
import      Numeral.Natural.Relation.Order as [≤def]
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Relator.Ordering
open import Structure.Function
open import Structure.Function.Domain
open import Syntax.Function
open import Syntax.Transitivity

_≤_ : ℕ → ℕ → Stmt
_≤_ a b = ∃{Obj = ℕ}(n ↦ a + n ≡ b)

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_) (_<_) public

[≤]-with-[𝐒] : ∀{a b : ℕ} → (a ≤ b) → (𝐒(a) ≤ 𝐒(b))
[≤]-with-[𝐒] {a} {b} ([∃]-intro n ⦃ f ⦄) =
  [∃]-intro n ⦃
    𝐒(a) + n 🝖[ _≡_ ]-[ [+]-stepₗ {a} {n} ]
    𝐒(a + n) 🝖[ _≡_ ]-[ congruence₁(𝐒) f ]
    𝐒(b) 🝖-end
  ⦄

[≤]-equivalence : ∀{x y} → (x ≤ y) ↔ (x [≤def].≤ y)
[≤]-equivalence{x}{y} = [↔]-intro (l{x}{y}) (r{x}{y}) where
  l : ∀{x y} → (x ≤ y) ← (x [≤def].≤ y)
  l{𝟎}   {y}    ([≤def].min)      = [∃]-intro(y) ⦃ [≡]-intro ⦄
  l{𝐒(x)}{𝟎}    ()
  l{𝐒(x)}{𝐒(y)} ([≤def].succ proof) = [≤]-with-[𝐒] {x}{y} (l{x}{y} (proof))

  r : ∀{x y} → (x ≤ y) → (x [≤def].≤ y)
  r{𝟎}   {y}    ([∃]-intro(z) ⦃ 𝟎+z≡y   ⦄) = [≤def].min
  r{𝐒(x)}{𝟎}    ([∃]-intro(z) ⦃ ⦄)
  r{𝐒(x)}{𝐒(y)} ([∃]-intro(z) ⦃ 𝐒x+z≡𝐒y ⦄) = [≤def].succ (r{x}{y} ([∃]-intro(z) ⦃ injective(𝐒)(𝐒x+z≡𝐒y) ⦄))
