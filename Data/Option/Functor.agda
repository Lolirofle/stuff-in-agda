module Data.Option.Functor where

import Lvl
import      Functional as Fn
open import Function.Equals
open import Data.Option
open import Data.Option.Proofs
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Sets.Setoid using (Function ; BinaryOperator)
import      Structure.Category.Functor as Functor
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Category

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  map-functor : Functor{ℓ}(Option)
  Functor.map(map-functor) = map
  Functor.map-function map-functor = map-function-eq
  Functor.op-preserving map-functor = map-preserves-[∘]
  Functor.id-preserving map-functor = map-preserves-id

instance
  andThen-monad : Monad{ℓ}(Option)
  Monad.η   andThen-monad _ = Some
  Monad.ext andThen-monad   = Fn.swap _andThen_
  Monad.ext-function andThen-monad = andThen-function-eq
  Monad.ext-inverse  andThen-monad = andThenᵣ-Some
  Dependent._⊜_.proof (Monad.ext-identity   andThen-monad) = [≡]-intro
  Dependent._⊜_.proof (Monad.ext-distribute andThen-monad {f = f} {g}) {x} = andThen-associativity {f = g}{g = f}{o = x}

{-
module _ {_▫_ : T → T → T} ⦃ monoid : Monoid(_▫_) ⦄ where
  open Monoid(monoid)

  instance
    combine-monoid : Monoid(Same.combine(_▫_))
    BinaryOperator.congruence (Monoid.binary-operator combine-monoid) p₁ p₂ = {!!}
    Associativity.proof (Monoid.associativity combine-monoid) = {!!}
    ∃.witness (Monoid.identity-existence combine-monoid) = Some id
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence combine-monoid))) = {!!}
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence combine-monoid))) = {!!}
-}
