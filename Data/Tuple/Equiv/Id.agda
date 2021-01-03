module Data.Tuple.Equiv.Id where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Type

private variable ℓ ℓₒ₁ ℓₒ₂ : Lvl.Level
private variable A B : Type{ℓ}
private variable f g : A → B
private variable p : A ⨯ B

instance
  Tuple-Id-extensionality : Extensionality{A = A}{B = B}([≡]-equiv)
  Tuple-Id-extensionality = intro

Tuple-left-map : (Tuple.left(Tuple.map f g p) ≡ f(Tuple.left(p)))
Tuple-left-map = [≡]-intro

Tuple-right-map : (Tuple.right(Tuple.map f g p) ≡ g(Tuple.right(p)))
Tuple-right-map = [≡]-intro
