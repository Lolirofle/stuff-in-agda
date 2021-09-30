module Numeral.Natural.Relation.Proofs where

open import Data
open import Functional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Relator.Equals
open import Type

private variable n a b : ℕ

Positive-non-zero : Positive(n) ↔ (n ≢ 𝟎)
Positive-non-zero {𝟎}   = [↔]-intro (apply [≡]-intro) \()
Positive-non-zero {𝐒 n} = [↔]-intro (const <>) (const \())

Positive-greater-than-zero : Positive(n) ↔ (n > 𝟎)
Positive-greater-than-zero = [↔]-transitivity Positive-non-zero ([↔]-intro [>]-to-[≢] [≢]-to-[<]-of-0ᵣ)

Positive-greater-than : Positive(a) ← (a > b)
Positive-greater-than {a}   {𝟎}   ab = [↔]-to-[←] Positive-greater-than-zero ab
Positive-greater-than {𝐒 a} {𝐒 b} ab = <>

Positive-not-[+] : (a ≢ a + b) → Positive(b)
Positive-not-[+] {a} {𝟎}   p with () ← p [≡]-intro
Positive-not-[+] {a} {𝐒 b} _ = <>
