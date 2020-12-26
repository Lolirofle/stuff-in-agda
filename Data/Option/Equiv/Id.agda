module Data.Option.Equiv.Id where

import      Lvl
open import Data.Option
open import Data.Option.Equiv
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Some-injectivity : Injective {B = Option(T)} (Some)
  Injective.proof Some-injectivity [≡]-intro = [≡]-intro

instance
  Id-Option-extensionality : Extensionality{A = T} ([≡]-equiv)
  Extensionality.cases-inequality Id-Option-extensionality ()
