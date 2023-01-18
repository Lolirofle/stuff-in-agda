{-# OPTIONS --cubical #-}

module Data.Option.Equiv.Path where

import      Lvl
open import BidirectionalFunction using (_$ₗ_ ; _$ᵣ_ ; intro)
open import Data
open import Data.Option
open import Data.Option.Functions as Option using (_or_)
open import Data.Option.Functions.Unmap
open import Data.Option.Functions.Unmap.Proofs
open import Data.Option.Equiv as Option
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Operator
open import Structure.Relator
import      Type.Cubical.Isomorphism as Iso
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path.Univalence
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}

instance
  Some-injectivity : Injective {B = Option(T)} (Some)
  Injective.proof Some-injectivity {x}{y} = congruence₂-₁(_or_)(x)

instance
  Path-Option-extensionality : Extensionality{A = T} (Path-equiv)
  Extensionality.cases-inequality (Path-Option-extensionality {T = T}) {x} p with () ← substitute₁ᵣ(elim{A = T}{B = λ _ → Type}(Option(T)) (const Empty)) p (Some x)

Option-[≍]-injective : (Option A Iso.≍ Option B) → (A Iso.≍ B)
Option-[≍]-injective {A = A}{B = B} ([∃]-intro f ⦃ intro ⦄) = [∃]-intro
  (intro
    (unmap(f $ₗ_) ⦃ inverseₗ-to-injective ⦄)
    (unmap(f $ᵣ_) ⦃ inverseₗ-to-injective ⦄)
  )
  ⦃ intro
    ⦃ left  = unmap-inverseᵣ ⦃ inj = _ ⦄ ⦄
    ⦃ right = unmap-inverseᵣ ⦃ inj = _ ⦄ ⦄
  ⦄

instance
  Option-injective : Injective(Option{ℓ})
  Option-injective = intro([↔]-to-[←] type-extensionality ∘ Option-[≍]-injective ∘ [↔]-to-[→] type-extensionality)
