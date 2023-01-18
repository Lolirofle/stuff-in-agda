module Numeral.Finite.Type where

open import Numeral.Finite
open import Numeral.Natural

module _ where
  open import Data
  open import Logic.Predicate
  open import Logic.Propositional
  open import Numeral.Finite.Proofs
  open import Numeral.Finite.SequenceTransform
  open import Numeral.Finite.SequenceTransform.Proofs
  import      Numeral.Natural.Relation.Order as ℕ
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Function.Domain
  open import Structure.Relator.Properties
  open import Type.Properties.MereProposition
  open import Type.Properties.Proofs
  open import Type.Size

  [≤][≼]-𝕟-compatibility : ∀{a b} → (a ℕ.≤ b) ↔ (𝕟(a) ≼ 𝕟(b))
  [≤][≼]-𝕟-compatibility = [↔]-intro l r where
    l : ∀{a b} → (a ℕ.≤ b) ← (𝕟(a) ≼ 𝕟(b))
    l{𝟎}     {b}     ([∃]-intro f) = ℕ.min
    l{𝐒 a}   {𝟎}     ([∃]-intro f) with () ← f(𝟎)
    l{𝐒 a}   {𝐒(𝐒 b)}([∃]-intro f) = ℕ.succ(l{a}{𝐒 b} ([∃]-intro (popShiftMap f) ⦃ popShiftMap-injective ⦄))
    l{𝐒 𝟎}   {𝐒 𝟎}   ([∃]-intro f) = ℕ.succ ℕ.min
    l{𝐒(𝐒 a)}{𝐒 𝟎}   ([∃]-intro f) with () ← injective(f) {𝟎}{𝐒 𝟎} (uniqueness(𝕟(1)) ⦃ inst = unit-is-prop ⦄)

    r : ∀{a b} → (a ℕ.≤ b) → (𝕟(a) ≼ 𝕟(b))
    r ℕ.min       = [∃]-intro (\()) ⦃ intro \{} ⦄
    r (ℕ.succ ab) =
      let [∃]-intro f = r ab
      in  [∃]-intro (prependIdMap f) ⦃ prependIdMap-injective ⦄

  {-
  -- TODO: One can use [≼]-to-[≽]-for-inhabited to prove that there is a surjection. The classical-fiber-existence parameter should hold for 𝕟 because it is finite (use linear search)
  [≥][≽]-𝕟-compatibility : ∀{a b} → (a ℕ.≥ b) ↔ (𝕟(a) ≽ 𝕟(b))
  [≥][≽]-𝕟-compatibility = [↔]-intro l r where
    l : ∀{a b} → (a ℕ.≥ b) ← (𝕟(a) ≽ 𝕟(b))
    l{a}  {𝟎}      ([∃]-intro f) = ℕ.min
    l{𝟎}  {𝐒 b}    ([∃]-intro f) with () ← [∃]-witness(surjective(f) {𝟎})
    l{𝐒 a}{𝐒 𝟎}    ([∃]-intro f) = ℕ.succ ℕ.min
    l{𝐒 a}{𝐒(𝐒 b)} ([∃]-intro f) = ℕ.succ(l{a}{𝐒 b} ([∃]-intro (popShiftMap f) ⦃ {!!} ⦄))

    r : ∀{a b} → (a ℕ.≥ b) → (𝕟(a) ≽ 𝕟(b))
    r ab = {!!}
  -}

  open import Logic.Classical
  open import Numeral.Natural.Relation.Order.Proofs
  open import Numeral.Natural.Decidable
  open import Type.Size.Proofs
  open import Type.Properties.Decidable.Proofs

  instance
    𝕟-injective : Injective(𝕟)
    𝕟-injective =
      intro(contrapositiveₗ ⦃ decider-to-classical ⦄ \nxy nxny →
        nxy(antisymmetry(ℕ._≤_)(_≡_)
          ([↔]-to-[←] [≤][≼]-𝕟-compatibility (sub₂(_≡_)(\A B → A ≼ B) nxny))
          ([↔]-to-[←] [≤][≼]-𝕟-compatibility (sub₂(_≡_)(\A B → A ≼ B) (symmetry(_≡_) nxny)))
        )
      )

{-
open import Functional
import      Lvl
open import Type
open import Syntax.Function

module _ where
  open import Data
  open import Data.Option
  open import Relator.Equals
  -- open import Relator.Equals.Proofs.Equiv
  open import Relator.Equals.Proofs
  open import Structure.Function

  𝕟' : ℕ → Type{Lvl.𝟎}
  𝕟'(𝟎)   = Empty
  𝕟'(𝐒 n) = Option(𝕟'(n))

  Option-injective : ∀{ℓ}{a b : Type{ℓ}} → (Option(a) ≡ Option(b)) → (a ≡ b)
  Option-injective p = [≡]-unsubstitution \{f} fa → {!!}

  𝕟'-injective : ∀{a b} → (𝕟'(a) ≡ 𝕟'(b)) → (a ≡ b)
  𝕟'-injective {𝟎} {𝟎} p = [≡]-intro
  𝕟'-injective {𝟎} {𝐒 b} p = {!!}
  𝕟'-injective {𝐒 a} {𝟎} p = {!!}
  𝕟'-injective {𝐒 a} {𝐒 b} p = congruence₁(𝐒) (𝕟'-injective {a}{b} (Option-injective p))
-}
