module Numeral.Finite.Bound.Proofs where

open import Data.Boolean.Stmt
open import Functional
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Proofs
open import Numeral.Natural
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names

private variable N : ℕ

bound-[≤?]-injective : ∀{a b} .⦃ ord : IsTrue(a ℕ.≤? b) ⦄ → Injective(bound-[≤?] {a}{b})
bound-[≤?]-injective = intro proof where
  proof : ∀{a b} .⦃ ord : IsTrue(a ℕ.≤? b) ⦄ → Names.Injective(bound-[≤?] {a}{b})
  proof{𝐒 _}{𝐒 _}{𝟎}  {𝟎}   = const [≡]-intro
  proof{𝐒 a}{𝐒 b}{𝐒 x}{𝐒 y} = congruence₁(𝐒) ∘ proof{x = x}{y} ∘ injective(𝐒)
