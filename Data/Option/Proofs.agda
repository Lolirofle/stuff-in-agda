module Data.Option.Proofs where

import      Lvl
open import Data.Option
open import Data.Either
open import Data.Either.Proofs
open import Relator.Equals
open import Type

module _ {ℓ} {T : Type{ℓ}} where -- TODO: This does not seem to work?
  Some-injectivity : ∀{x y : T} → (Right{ℓ}{ℓ}{T}{T}(x) ≡ Right(y)) → (x ≡ y)
  Some-injectivity = Right-injectivity
