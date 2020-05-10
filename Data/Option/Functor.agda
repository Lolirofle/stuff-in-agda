module Data.Option.Functor where

import Lvl
import      Functional as Fn
open import Function.Equals
open import Data.Option
open import Data.Option.Proofs
open import Lang.Instance
open import Logic
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
import      Structure.Category.Functor as Functor
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Category

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- Option is a functor by using `map`.
instance
  map-functor : Functor{ℓ}(Option)
  Functor.map           ⦃ map-functor ⦄ = map
  Functor.map-function  ⦃ map-functor ⦄ = map-function-eq
  Functor.op-preserving ⦃ map-functor ⦄ = map-preserves-[∘]
  Functor.id-preserving ⦃ map-functor ⦄ = map-preserves-id

-- Option is a monad by using `andThen`.
instance
  andThen-monad : Monad{ℓ}(Option)
  Monad.η            ⦃ andThen-monad ⦄ _ = Some
  Monad.ext          ⦃ andThen-monad ⦄   = Fn.swap _andThen_
  Monad.ext-function ⦃ andThen-monad ⦄ = andThen-function-eq
  Monad.ext-inverse  ⦃ andThen-monad ⦄ = andThenᵣ-Some
  Dependent._⊜_.proof (Monad.ext-identity   ⦃ andThen-monad ⦄) = [≡]-intro
  Dependent._⊜_.proof (Monad.ext-distribute ⦃ andThen-monad ⦄ {f = f} {g}) {x} = andThen-associativity {f = g}{g = f}{o = x}

-- A monoid is constructed by lifting an associative binary operator using `or-combine`.
-- Essentially means that an additional value (None) is added to the type, and it becomes an identity by definition.
module _ {_▫_ : T → T → T} where
  instance
    or-combine-monoid : ⦃ assoc : Associativity(_▫_) ⦄ → Monoid(or-combine(_▫_) Fn.id Fn.id)
    Associativity.proof (Monoid.associativity or-combine-monoid) {None}   {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {None}   {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {None}   {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {None}   {Some y} {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {Some x} {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {Some x} {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {Some x} {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity or-combine-monoid) {Some x} {Some y} {Some z} = [≡]-with(Some) (associativity(_▫_))
    ∃.witness (Monoid.identity-existence or-combine-monoid) = None
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence or-combine-monoid))) {None}   = [≡]-intro
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence or-combine-monoid))) {Some x} = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence or-combine-monoid))) {None}   = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence or-combine-monoid))) {Some x} = [≡]-intro

module _ {_▫_ : T → T → T} where
  open Monoid ⦃ … ⦄ using (id)

  -- A monoid is still a monoid when lifting a binary operator using `and-combine`.
  instance
    and-combine-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(and-combine(_▫_))
    Associativity.proof (Monoid.associativity and-combine-monoid) {None}   {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {None}   {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {None}   {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {None}   {Some y} {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {Some x} {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {Some x} {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {Some x} {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity and-combine-monoid) {Some x} {Some y} {Some z} = [≡]-with(Some) (associativity(_▫_))
    ∃.witness (Monoid.identity-existence and-combine-monoid) = Some(id)
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence and-combine-monoid))) {None}   = [≡]-intro
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence and-combine-monoid))) {Some x} = [≡]-with(Some) (identityₗ(_▫_)(_))
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence and-combine-monoid))) {None}   = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence and-combine-monoid))) {Some x} = [≡]-with(Some) (identityᵣ(_▫_)(_))

  instance
    and-combine-absorberₗ : Absorberₗ(and-combine(_▫_))(None)
    Absorberₗ.proof and-combine-absorberₗ = [≡]-intro

  instance
    and-combine-absorberᵣ : Absorberᵣ(and-combine(_▫_))(None)
    Absorberᵣ.proof and-combine-absorberᵣ {None}   = [≡]-intro
    Absorberᵣ.proof and-combine-absorberᵣ {Some x} = [≡]-intro

  -- `and-combine` essentially adds an additional value (None) to the type, and it becomes an absorber by definition.
  instance
    and-combine-absorber : Absorber(and-combine(_▫_))(None)
    and-combine-absorber = intro
