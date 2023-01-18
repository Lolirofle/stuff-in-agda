module Data.Option.Categorical where

import Lvl
import      Functional as Fn
open import Data.Option
import      Data.Option.Equiv as Option
open import Data.Option.Functions
open import Data.Option.Proofs
import      Function.Equiv as Function
open import Function.Equiv.Proofs
open import Logic.Propositional
open import Structure.Categorical.Functor.Properties
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Category.Functor
open import Type.Category.Monad

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B : Type{ℓ}

module _
  {equiv-B        : Equiv{ℓₑ₁}(B)} (let instance _ = equiv-B)
  {equiv-option-B : Equiv{ℓₑ₂}(Option B)} (let instance _ = equiv-option-B)
  {equiv-func     : Equiv{ℓₑ₃}(A → B)} (let instance _ = equiv-func)
  {equiv-func-opt : Equiv{ℓₑ₄}(Option A → Option B)} (let instance _ = equiv-func-opt)
  ⦃ some-func : Function(Some) ⦄
  ⦃ ext : Function.Extensionality{A = A}{B = B} equiv-B equiv-func ⦄
  ⦃ ext-opt : Function.Extensionality{A = Option A}{B = Option B} equiv-option-B equiv-func-opt ⦄
  where

  instance
    map-function : Function(map {A = A}{B = B})
    map-function =
      intro(\p → [↔]-to-[→] Function.pointwiseEquality \{
        {None}   → reflexivity(_≡_) ;
        {Some _} → congruence₁(Some) ([↔]-to-[←] Function.pointwiseEquality p)
      })

module _
  {equiv-option-B : Equiv{ℓₑ}(Option B)} (let instance _ = equiv-option-B)
  {equiv-func     : Equiv{ℓₑ₁}(A → Option B)} (let instance _ = equiv-func)
  {equiv-func-opt : Equiv{ℓₑ₂}(Option A → Option B)} (let instance _ = equiv-func-opt)
  ⦃ ext : Function.Extensionality{A = A}{B = Option B} equiv-option-B equiv-func ⦄
  ⦃ ext-opt : Function.Extensionality{A = Option A}{B = Option B} equiv-option-B equiv-func-opt ⦄
  where

  instance
    andThen-function : Function(Fn.swap(_andThen_ {T₁ = A}{T₂ = B}))
    andThen-function = intro(\p → [↔]-to-[→] Function.pointwiseEquality \{
        {None}   → reflexivity(_≡_) ;
        {Some _} → [↔]-to-[←] Function.pointwiseEquality p
      })

module _
  {equiv-type : ∀{T : Type{ℓ}} → Equiv{ℓₑ₁}(T)} (let instance _ = equiv-type)
  ⦃ ext-option : ∀{T : Type{ℓ}} → Option.Extensionality(equiv-type{T = Option T}) ⦄
  {equiv-func : ∀{A B : Type{ℓ}} → Equiv{ℓₑ₂}(A → B)} (let instance _ = equiv-func)
  ⦃ func : ∀{A B : Type{ℓ}}{f : A → B} → Function(f) ⦄
  ⦃ ext : ∀{A B : Type{ℓ}} → Function.Extensionality{A = A}{B = B} equiv-type equiv-func ⦄
  where

  private open module EquivType{T} = Equiv(equiv-type{T}) using () renaming (_≡_ to _≡ₜ_)
  private open module EquivFunc{A}{B} = Equiv(equiv-func{A}{B}) using () renaming (_≡_ to _≡f_)

  -- Option is a functor by using `map`.
  instance
    map-functor : Functor{ℓ}(Option)
    Functor.map           ⦃ map-functor ⦄ = map
    Functor.op-preserving ⦃ map-functor ⦄ = intro ([↔]-to-[→] Function.pointwiseEquality (\{x} → map-preserves-[∘] {x = x}))
    Functor.id-preserving ⦃ map-functor ⦄ = intro ([↔]-to-[→] Function.pointwiseEquality map-preserves-id)

  -- Option is a monad by using `andThen`.
  instance
    andThen-monad : Monad{ℓ}(Option)
    Monad.η            ⦃ andThen-monad ⦄ _ = Some
    Monad.ext          ⦃ andThen-monad ⦄   = Fn.swap(_andThen_)
    Monad.ext-inverse  ⦃ andThen-monad ⦄ = [↔]-to-[→] Function.pointwiseEquality (\{x} → andThenᵣ-Some{x = x})
    Monad.ext-identity   ⦃ andThen-monad ⦄ = reflexivity(_≡f_)
    Monad.ext-distribute ⦃ andThen-monad ⦄ {f = f}{g = g} = [↔]-to-[→] Function.pointwiseEquality (\{x} → andThen-associativity {f = g}{g = f}{o = x})
