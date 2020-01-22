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
open import Structure.Category.Functor
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type
open import Type.Category

map-functor : ∀{ℓ} → TypeFunctor{ℓ}(List)
Functor.map(map-functor) = map
_⊜_.proof (Functor.op-preserving map-functor {A} {B} {C} {f} {g}) {l} = map-preserves-[∘]
_⊜_.proof (Functor.id-preserving map-functor {x}) = map-preserves-id
