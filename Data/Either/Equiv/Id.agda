module Data.Either.Equiv.Id where

import      Lvl
open import Data
open import Data.Either as Either
open import Data.Either.Equiv
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid
open import Structure.Function.Domain
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    Left-injectivity : Injective(Left{A = A}{B = B})
    Injective.proof Left-injectivity [≡]-intro = [≡]-intro

  instance
    Right-injectivity : Injective(Right{A = A}{B = B})
    Injective.proof Right-injectivity [≡]-intro = [≡]-intro

  instance
    Either-Id-extensionality : Extensionality{A = A}{B = B} [≡]-equiv
    Either-Id-extensionality = intro \()
