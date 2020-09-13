module Data.Boolean.Functions where

open import Data.Boolean
open import Type

elim : ∀{ℓ}{P : Bool → Type{ℓ}} → P(𝐹) → P(𝑇) → (∀{b} → P(b))
elim f t {𝑇} = t
elim f t {𝐹} = f
