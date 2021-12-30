module Numeral.Finite.SequenceTransform.Proofs where

open import Data
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Numeral.Finite
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Proofs
open import Numeral.Finite.Proofs
open import Numeral.Finite.SequenceTransform
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names

prependIdMap-injective : ∀{a b}{f : 𝕟(a) → 𝕟(b)} → ⦃ Injective(f) ⦄ → Injective(prependIdMap f)
prependIdMap-injective {f = f} = intro proof where
  proof : Names.Injective(prependIdMap f)
  proof {𝟎} {𝟎}     = const [≡]-intro
  proof {𝐒 x} {𝐒 y} = congruence₁(𝐒) ∘ injective(f) ∘ injective(𝐒)

popShiftMap-injective : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒(a)) → 𝕟(𝐒(b))} → ⦃ Injective(f) ⦄ → Injective(popShiftMap f)
popShiftMap-injective {f = f} = intro proof where
  proof : Names.Injective(popShiftMap f)
  proof {x} {y} = injective(𝐒) ∘ injective(f) ∘ shiftRepeat'-almost-injective
    ⦃ cx = [↔]-to-[→] [≢][≢?]-equivalence (contrapositiveᵣ(injective(f)) \()) ⦄
    ⦃ cy = [↔]-to-[→] [≢][≢?]-equivalence (contrapositiveᵣ(injective(f)) \()) ⦄

-- popShiftMap-surjective : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒(a)) → 𝕟(𝐒(b))} → ⦃ Surjective(f) ⦄ → Surjective(popShiftMap f)
-- popShiftMap-surjective {a} {b} {f = f} = intro ([∃]-intro {!prependIdMap(surjective(f))!} ⦃ {!!} ⦄)
-- popShiftMap-surjective {𝟎} {𝐒 b} {f = f} = intro([∃]-intro {![∃]-proof(surjective(f) {𝐒 𝟎})!} ⦃ {![∃]-witness(surjective(f))!} ⦄)
-- popShiftMap-surjective {𝐒 a} {𝐒 b} {f = f} = {!!}

open import Function.Equals
import      Numeral.Finite.Relation.Order as 𝕟
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type.Properties.Singleton

{-
-- TODO: Use shiftRepeat-def1, shiftRepeat-def2 and shiftRepeat-shiftRepeat'-eq
popShiftMap-def1 : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒 a) → 𝕟(𝐒 b)}{x} → (f(𝐒(x)) 𝕟.≤ f(𝟎)) → (popShiftMap f(x) 𝕟.≡ f(𝐒(x)))
popShiftMap-def1 {𝐒 a} {𝐒 b} {f}{x} = {!!}

popShiftMap-def2 : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒 a) → 𝕟(𝐒 b)}{x} → (f(𝐒(x)) 𝕟.> f(𝟎)) → (𝐒(popShiftMap f(x)) 𝕟.≡ f(𝐒(x)))
popShiftMap-def2 {𝐒 a} {𝐒 b} {f}{x} = {!!}
-}

popShiftMap-inverseᵣ : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ → Inverseᵣ ⦃ [⊜]-equiv ⦄ (popShiftMap)(prependIdMap{a}{b})
popShiftMap-inverseᵣ = intro p where
  p : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ → Names.Inverses ⦃ [⊜]-equiv ⦄ (popShiftMap)(prependIdMap{a}{b})
  p {a}   {𝐒(𝐒(b))} = reflexivity(_⊜_)
  p {𝟎}   {𝐒(𝟎)}    = intro \{}
  p {𝐒(a)}{𝐒(𝟎)}    = intro(symmetry(_≡_) unit-uniqueness)

{-
-- TODO: Not true. The inverse should remove the f(0) to something, not 0
popShiftMap-value-inverseᵣ : ∀{a b} ⦃ pos-a : ℕ.Positive(a) ⦄ ⦃ pos-b : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒 a) → 𝕟(𝐒 b)}{f⁻¹} → Inverseᵣ(popShiftMap f)(popShiftMap f⁻¹)
popShiftMap-value-inverseᵣ = intro(p) where
  p : ∀{a b} ⦃ pos-a : ℕ.Positive(a) ⦄ ⦃ pos-b : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒 a) → 𝕟(𝐒 b)}{f⁻¹} → Names.Inverses(popShiftMap f)(popShiftMap f⁻¹)
  p {𝐒 𝟎} {𝐒 𝟎} {f = f} {f⁻¹} {x} = {!!}
  p {𝐒 𝟎} {𝐒 (𝐒 b)} {f = f} {f⁻¹} {x} = {!!}
  p {𝐒 (𝐒 a)} {𝐒 𝟎} {f = f} {f⁻¹} {x} = {!!}
  p {𝐒 (𝐒 a)} {𝐒 (𝐒 b)} {f = f} {f⁻¹} {x} =
    (popShiftMap f ∘ popShiftMap f⁻¹) x                        🝖[ _≡_ ]-[]
    shiftRepeat'(f(𝟎)) (f(𝐒(shiftRepeat'(f⁻¹(𝟎)) (f⁻¹(𝐒 x))))) 🝖[ _≡_ ]-[ {!!} ]
    x                                                          🝖-end

open import Syntax.Number
a : 𝕟(5) → 𝕟(5)
a 𝟎 = 3
a(𝐒 𝟎) = 0
a(𝐒(𝐒 𝟎)) = 4
a(𝐒(𝐒(𝐒 𝟎))) = 2
a(𝐒(𝐒(𝐒(𝐒 𝟎)))) = 1

b : 𝕟(5) → 𝕟(5)
b(𝐒(𝐒(𝐒 𝟎))) = 0
b(𝐒(𝐒(𝐒(𝐒 𝟎)))) = 2
b(𝐒 𝟎) = 2
b(𝐒(𝐒 𝟎)) = 3
b 𝟎 = 4

test = {!\x → popShiftMap2 a (popShiftMap2 b x)!}
-}
{-
popShiftMap-surjective : ∀{a b} ⦃ pos-a : ℕ.Positive(a) ⦄ ⦃ pos-b : ℕ.Positive(b) ⦄ {f : 𝕟(𝐒(a)) → 𝕟(𝐒(b))} → ⦃ Surjective(f) ⦄ → Surjective(popShiftMap f)
popShiftMap-surjective {a} {b} {f = f} = intro(\{y} → [∃]-intro (popShiftMap(\y → [∃]-witness(surjective(f) {y})) y) ⦃ {!!} ⦄)
popShiftMap-surjective {𝐒 𝟎} {𝐒 b} {f = f} = intro([∃]-intro {![∃]-proof(surjective(f) {𝐒 𝟎})!} ⦃ {![∃]-witness(surjective(f))!} ⦄)
-}
