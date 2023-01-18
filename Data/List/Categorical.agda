module Data.List.Categorical where

import Lvl
open import Data.List
open import Data.List.Functions
open import Data.List.Proofs
import      Data.List.Equiv as List
open import Data.List.Equiv.Id
import      Function.Equiv as Function
open import Function.Equiv.Proofs
open import Logic.Propositional
open import Structure.Categorical.Functor.Properties
open import Structure.Function
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type
open import Type.Category.Functor
open import Type.Category.Monad
open import Type.Identity
open import Type.Identity.Proofs

private variable ℓ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _
  {equiv-type : ∀{T : Type{ℓ}} → Equiv{ℓₑ₁}(T)} (let instance _ = equiv-type)
  ⦃ ext-list : ∀{T : Type{ℓ}} → List.Extensionality(equiv-type{T = List T}) ⦄
  {equiv-func : ∀{A B : Type{ℓ}} → Equiv{ℓₑ₂}(A → B)} (let instance _ = equiv-func)
  ⦃ func : ∀{A B : Type{ℓ}}{f : A → B} → Function(f) ⦄
  ⦃ ext : ∀{A B : Type{ℓ}} → Function.Extensionality{A = A}{B = B} equiv-type equiv-func ⦄
  where

  private open module EquivType{T} = Equiv(equiv-type{T}) using () renaming (_≡_ to _≡ₜ_)

  instance
    map-functor : Functor(List)
    Functor.map ⦃ map-functor ⦄ = map
    Function.congruence (Functor.map-function ⦃ map-functor ⦄) proof = [↔]-to-[→] Function.pointwiseEquality (map-operator-raw ⦃ func-fg = [∨]-introₗ func ⦄ ([↔]-to-[←] Function.pointwiseEquality proof) (reflexivity(_≡_) ⦃ Equiv.reflexivity equiv-type ⦄))
    Functor.op-preserving ⦃ map-functor ⦄ = intro ([↔]-to-[→] Function.pointwiseEquality(sub₂(Id)(_≡ₜ_) map-preserves-[∘]))
    Functor.id-preserving ⦃ map-functor ⦄ = intro ([↔]-to-[→] Function.pointwiseEquality(sub₂(Id)(_≡ₜ_) map-preserves-id))

  instance
    concatMap-monad : Monad(List)
    Monad.η   ⦃ concatMap-monad ⦄ _ = singleton
    Monad.ext ⦃ concatMap-monad ⦄   = concatMap
    Function.congruence (Monad.ext-function ⦃ concatMap-monad ⦄) {f}{g} proof = [↔]-to-[→] Function.pointwiseEquality (\{l} → concatMap-operator {f = f}{g = g} ⦃ func-fg = [∨]-introₗ func ⦄ {l} ([↔]-to-[←] Function.pointwiseEquality proof) (reflexivity(_≡_) ⦃ Equiv.reflexivity equiv-type ⦄))
    Monad.ext-inverse    ⦃ concatMap-monad ⦄ = [↔]-to-[→] Function.pointwiseEquality \{x} → sub₂(Id)(_≡ₜ_) (concatMap-singleton{x = x})
    Monad.ext-identity   ⦃ concatMap-monad ⦄ = [↔]-to-[→] Function.pointwiseEquality (identityᵣ(_++_)(∅))
    Monad.ext-distribute ⦃ concatMap-monad ⦄ {f = f}{g = g} = [↔]-to-[→] Function.pointwiseEquality \{x} → sub₂(Id)(_≡ₜ_) (concatMap-[∘] {f = f}{g = g}{x = x})
