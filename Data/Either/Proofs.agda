module Data.Either.Proofs where

import      Lvl
open import Data.Either
open import Relator.Equals
open import Type

module _ {ℓ₁}{ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
  Left-injectivity : ∀{x y : T₁} → (Left {T₁ = T₁} {T₂ = T₂} (x) ≡ Left(y)) → (x ≡ y)
  Left-injectivity [≡]-intro = [≡]-intro

  Right-injectivity : ∀{x y : T₂} → (Right {T₁ = T₁} {T₂ = T₂} (x) ≡ Right(y)) → (x ≡ y)
  Right-injectivity [≡]-intro = [≡]-intro
