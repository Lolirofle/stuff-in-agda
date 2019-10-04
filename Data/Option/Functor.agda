module Data.Option.Functor where

import Lvl
open import Functional
open import Functional.Equals
open import Data.Option
open import Data.Option.Proofs
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Category.Functor
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type
open import Type.Category

map-functor : ∀{ℓ} → TypeFunctor{ℓ}(Option)
Functor.map(map-functor) = map
_⊜_.proof (Functor.op-preserving map-functor {A} {B} {C} {f} {g}) {l} = [∘]-preserving-map
_⊜_.proof (Functor.id-preserving map-functor {x}) = [∘]-preserving-id
