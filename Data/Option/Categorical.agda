module Data.Option.Categorical where

import Lvl
import      Functional as Fn
open import Function.Equals
open import Data.Option
open import Data.Option.Functions
open import Data.Option.Proofs
open import Functional.Instance
open import Logic
open import Logic.Predicate
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
import      Structure.Category.Functor as Functor
open import Structure.Function
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
  Functor.map-function  ⦃ map-functor ⦄ = map-function
  Functor.op-preserving ⦃ map-functor ⦄ = map-preserves-[∘]
  Functor.id-preserving ⦃ map-functor ⦄ = map-preserves-id

-- Option is a monad by using `andThen`.
instance
  andThen-monad : Monad{ℓ}(Option)
  Monad.η            ⦃ andThen-monad ⦄ _ = Some
  Monad.ext          ⦃ andThen-monad ⦄   = Fn.swap _andThen_
  Monad.ext-function ⦃ andThen-monad ⦄ = andThen-function
  Monad.ext-inverse  ⦃ andThen-monad ⦄ = andThenᵣ-Some
  Dependent._⊜_.proof (Monad.ext-identity   ⦃ andThen-monad ⦄) = [≡]-intro
  Dependent._⊜_.proof (Monad.ext-distribute ⦃ andThen-monad ⦄ {f = f} {g}) {x} = andThen-associativity {f = g}{g = f}{o = x}

-- A monoid is constructed by lifting an associative binary operator using `orCombine`.
-- Essentially means that an additional value (None) is added to the type, and it becomes an identity by definition.
module _ {_▫_ : T → T → T} where
  instance
    orCombine-monoid : ⦃ assoc : Associativity(_▫_) ⦄ → Monoid(orCombine(_▫_) Fn.id Fn.id)
    Associativity.proof (Monoid.associativity orCombine-monoid) {None}   {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {None}   {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {None}   {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {None}   {Some y} {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {Some x} {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {Some x} {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {Some x} {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity orCombine-monoid) {Some x} {Some y} {Some z} = congruence₁(Some) (associativity(_▫_))
    ∃.witness (Monoid.identity-existence orCombine-monoid) = None
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence orCombine-monoid))) {None}   = [≡]-intro
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence orCombine-monoid))) {Some x} = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence orCombine-monoid))) {None}   = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence orCombine-monoid))) {Some x} = [≡]-intro

module _ {_▫_ : T → T → T} where
  open Monoid ⦃ … ⦄ using (id)

  -- A monoid is still a monoid when lifting a binary operator using `andCombine`.
  instance
    andCombine-monoid : ⦃ monoid : Monoid(_▫_) ⦄ → Monoid(andCombine(_▫_))
    Associativity.proof (Monoid.associativity andCombine-monoid) {None}   {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {None}   {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {None}   {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {None}   {Some y} {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {Some x} {None}   {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {Some x} {None}   {Some z} = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {Some x} {Some y} {None}   = [≡]-intro
    Associativity.proof (Monoid.associativity andCombine-monoid) {Some x} {Some y} {Some z} = congruence₁(Some) (associativity(_▫_))
    ∃.witness (Monoid.identity-existence andCombine-monoid) = Some(id)
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence andCombine-monoid))) {None}   = [≡]-intro
    Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence andCombine-monoid))) {Some x} = congruence₁(Some) (identityₗ(_▫_)(_))
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence andCombine-monoid))) {None}   = [≡]-intro
    Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence andCombine-monoid))) {Some x} = congruence₁(Some) (identityᵣ(_▫_)(_))

  instance
    andCombine-absorberₗ : Absorberₗ(andCombine(_▫_))(None)
    Absorberₗ.proof andCombine-absorberₗ {None}   = [≡]-intro
    Absorberₗ.proof andCombine-absorberₗ {Some x} = [≡]-intro

  instance
    andCombine-absorberᵣ : Absorberᵣ(andCombine(_▫_))(None)
    Absorberᵣ.proof andCombine-absorberᵣ {None}   = [≡]-intro
    Absorberᵣ.proof andCombine-absorberᵣ {Some x} = [≡]-intro

  -- `andCombine` essentially adds an additional value (None) to the type, and it becomes an absorber by definition.
  instance
    andCombine-absorber : Absorber(andCombine(_▫_))(None)
    andCombine-absorber = intro
