module Numeral.Natural.Proofs.HLevel where

{-
import Lvl
open import Numeral.Natural
open import Numeral.Natural.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain

open import Type
private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable f g : A → B

test : ∀{x y : B}{eq : x ≡ y}{f : A → B}{g : B → A} → congruence₁(f) ⦃ [≡]-function ⦄ (congruence₁(g) ⦃ [≡]-function ⦄ eq) ≡ eq
test {eq = [≡]-intro} = {!!}

ℕ-set : ∀{x y : ℕ}{l r : x ≡ y} → (l ≡ r)
ℕ-set {𝟎} {𝟎} {[≡]-intro} {[≡]-intro} = [≡]-intro
ℕ-set {𝐒 x} {𝐒 y} {l} {r} = {!congruence₁(congruence₁(𝐒)) (ℕ-set {x}{y}{congruence₁(𝐏) l}{congruence₁(𝐏) r})!}
-}
