module Structure.Numeral.Integer where

import      Lvl
open import Structure.Setoid.WithLvl
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.OrderedField
open import Structure.Relator
open import Type

private variable ℓₒ ℓₗ ℓₑ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable Z : Type{ℓₒ}

record Integer ⦃ equiv : Equiv{ℓₑ}(Z) ⦄ (_+_ : Z → Z → Z) (_⋅_ : Z → Z → Z) (_≤_ : Z → Z → Type{ℓₗ}) : Typeω where
  constructor intro
  field
    ⦃ ring ⦄              : Ring(_+_)(_⋅_)
    ⦃ ordered ⦄           : Ordered(_+_)(_⋅_)(_≤_)
  open Ring(ring) public
  open Ordered(ordered) public

  𝐒 : Z → Z
  𝐒 = _+ 𝟏

  𝐏 : Z → Z
  𝐏 = _− 𝟏

  field
    ⦃ distinct-identities ⦄ : DistinctIdentities
    positive-induction : ∀{ℓ}{P : Z → Type{ℓ}} ⦃ rel-p : UnaryRelator(P) ⦄ → P(𝟎) → (∀{n} → (𝟎 ≤ n) → P(n) → P(𝐒(n))) → (∀{n} → (𝟎 ≤ n) → P(n))
