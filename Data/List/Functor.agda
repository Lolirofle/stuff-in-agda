module Data.List.Functor where

import Lvl
open import Functional
open import Function.Equals
open import Data.List
open import Data.List.Proofs
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Setoid using (intro)
open import Structure.Function
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type
open import Type.Category

private variable ℓ : Lvl.Level

instance
  map-functor : Functor{ℓ}(List)
  Functor.map(map-functor) = map
  _⊜_.proof (Function.congruence (Functor.map-function map-functor) {x = f} {y = g} (intro proof)) = map-function-raw proof
  _⊜_.proof (Functor.op-preserving map-functor) = map-preserves-[∘]
  _⊜_.proof (Functor.id-preserving map-functor) = map-preserves-id

instance
  concatMap-monad : Monad{ℓ}(List)
  Monad.η   concatMap-monad _ = singleton
  Monad.ext concatMap-monad   = concatMap
  _⊜_.proof (Function.congruence (Monad.ext-function concatMap-monad) (intro proof)) {x} = concatMap-function-raw (proof) {x}
  Monad.ext-inverse    concatMap-monad = intro concatMap-singleton
  Monad.ext-identity   concatMap-monad = intro [≡]-intro
  Monad.ext-distribute concatMap-monad {f = f}{g = g} = intro (\{x} → concatMap-[∘] {f = f}{g = g}{x = x})
