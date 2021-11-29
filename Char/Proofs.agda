module Char.Proofs where

open import Char
open import Char.Functions
open import Functional
open import Logic.Predicate
open import Logic.IntroInstances
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain

module Primitives where
  primitive primCharToNatInjective : ∀(a)(b) → (unicodeCodePoint a ≡ unicodeCodePoint b) → (a ≡ b)

instance
  unicodeCodePoint-injective : Injective(unicodeCodePoint)
  Injective.proof unicodeCodePoint-injective {a}{b} = Primitives.primCharToNatInjective a b

open import Numeral.Natural
open import Numeral.Natural.Decidable
open import Operator.Equals
open import Type.Properties.Decidable as Decidable
open import Type.Properties.Decidable.Proofs
open import Structure.Function

-- TODO: ((ℕ._≡?_) on₂ unicodeCodePoint) is used here because it works. Char._≡?_ should be prefered, but it seems unprovable
instance
  Char-decidable-equiv : EquivDecidable(Char)
  ∃.witness Char-decidable-equiv = decide(2)(_≡_) on₂ unicodeCodePoint
  ∃.proof   Char-decidable-equiv {x}{y} =
    [↔]-to-[→]
      (decider-relator
        ([↔]-intro (congruence₁(unicodeCodePoint)) (injective(unicodeCodePoint)))
        [≡]-intro
      )
      (on₂-decider{f = unicodeCodePoint} (ℕ-equality-decider{unicodeCodePoint x}{unicodeCodePoint y}) {x}{y})
