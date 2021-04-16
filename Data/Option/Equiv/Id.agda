module Data.Option.Equiv.Id where

import      Lvl
open import Data.Option
open import Data.Option.Functions
open import Data.Option.Equiv
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable f : A → B
private variable o : Option T

instance
  Some-injectivity : Injective {B = Option(T)} (Some)
  Injective.proof Some-injectivity [≡]-intro = [≡]-intro

instance
  Id-Option-extensionality : Extensionality{A = T} ([≡]-equiv)
  Extensionality.cases-inequality Id-Option-extensionality ()

map-injectivity : ⦃ inj-f : Injective(f) ⦄ → Injective(map f)
Injective.proof map-injectivity           {None}   {None}   [≡]-intro = [≡]-intro
Injective.proof (map-injectivity {f = f}) {Some x} {Some y} p         = congruence₁(Some) (injective f(injective(Some) p))

-- TODO: Generalize and move
map-None : (map f o ≡ None) → (o ≡ None)
map-None {o = None} p = [≡]-intro
