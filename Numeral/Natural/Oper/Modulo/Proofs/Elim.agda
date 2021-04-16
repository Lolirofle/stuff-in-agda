module Numeral.Natural.Oper.Modulo.Proofs.Elim where

import Lvl
open import Data.Boolean.Stmt
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

mod-elim : ∀{ℓ} → (P : {ℕ} → ℕ → Type{ℓ}) → ∀{b} ⦃ _ : IsTrue(positive?(b)) ⦄ → (∀{a n} → (a < b) → P{a + (n ⋅ b)}(a)) → (∀{a} → P{a}(a mod b))
mod-elim P {𝐒 b} proof {a} with [<][≥]-dichotomy {a}{𝐒 b}
... | [∨]-introₗ lt = substitute₂(\x y → P{x}(y))
  (reflexivity(_≡_))
  (symmetry(_≡_) (mod-lesser-than-modulus ⦃ [≤]-without-[𝐒] lt ⦄))
  (proof{a}{0} lt)
... | [∨]-introᵣ ge = substitute₂(\x y → P{x}(y))
  ([↔]-to-[→] ([−₀][+]-nullify2ᵣ {(a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)}{a}) (subtransitivityᵣ(_≤_)(_≡_) ([≤]-of-[+]ₗ {(a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b)}{a mod 𝐒(b)}) ([⌊/⌋][mod]-is-division-with-remainder {a}{b})))
  (symmetry(_≡_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{b}))
  (proof{a −₀ ((a ⌊/⌋ 𝐒(b)) ⋅ 𝐒(b))}{a ⌊/⌋ 𝐒(b)} (subtransitivityₗ(_<_)(_≡_) (symmetry(_≡_) ([⌊/⌋][⋅]-inverseOperatorᵣ-error {a}{b})) (mod-maxᵣ{a}{𝐒 b})))
