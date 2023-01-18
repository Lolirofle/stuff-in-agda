module Char.Proofs where

open import Char
open import Char.Functions
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain

module Primitives where
  primitive primCharToNatInjective : ∀(a)(b) → (unicodeCodePoint a ≡ unicodeCodePoint b) → (a ≡ b)

instance
  unicodeCodePoint-injective : Injective(unicodeCodePoint)
  Injective.proof unicodeCodePoint-injective {a}{b} = Primitives.primCharToNatInjective a b
