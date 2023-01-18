module Functional.Setoid where

open import BidirectionalFunction using (_$ₗ_ ; _$ᵣ_)
import      Functional as Fn
open import Function.Proofs
open import Logic.Propositional
import      Lvl
open import Structure.Operator
open import Structure.Setoid
open import Structure.Setoid.Function
open import Syntax.Existential

private variable ℓ ℓₑ ℓₒ : Lvl.Level
private variable A B C A₁ A₂ A₃ A₄ : Setoid{ℓₑ}{ℓₒ}

_$_ : ◦(A →ₑₓₜ B) → (◦ A → ◦ B)
_$_ = ◦
infixl 0 _$_

id : ◦(A →ₑₓₜ A)
id = ⱻ Fn.id ⦃ id-function ⦄

_∘_ : ◦(B →ₑₓₜ C) → ◦(A →ₑₓₜ B) → ◦(A →ₑₓₜ C)
(ⱻ f) ∘ (ⱻ g) = ⱻ(f Fn.∘ g) ⦃ [∘]-function {f = f}{g = g} ⦄
infixl 10000 _∘_

const : ◦ B → ◦(A →ₑₓₜ B)
const c = ⱻ (Fn.const c) ⦃ const-function {c = c} ⦄

_∘ₛ_ : ◦(A →ₑₓₜ B →ₑₓₜ C) → ◦(A →ₑₓₜ B) → ◦(A →ₑₓₜ C)
f ∘ₛ (ⱻ g) with ⱻ f ← binaryOperatorExt $ₗ f = ⱻ (f Fn.∘ₛ g) ⦃ s-combinator-function {f = f}{g = g} ⦄
infixl 10000 _∘ₛ_

swap : ◦(A →ₑₓₜ B →ₑₓₜ C) → ◦(B →ₑₓₜ A →ₑₓₜ C)
swap f with ⱻ f ← binaryOperatorExt $ₗ f = binaryOperatorExt $ᵣ ⱻ(Fn.swap(f)) ⦃ swap-binaryOperator ⦄

_$₂ₓ_ : ◦(A →ₑₓₜ A →ₑₓₜ B) → ◦(A →ₑₓₜ B)
_$₂ₓ_ f = f ∘ₛ id

module Internal where
  constant : ◦(B →ₑₓₜ A →ₑₓₜ B)
  constant = binaryOperatorExt $ᵣ ⱻ Fn.const ⦃ intro Fn.const ⦄

  scompose : ◦((A →ₑₓₜ B →ₑₓₜ C) →ₑₓₜ (A →ₑₓₜ B) →ₑₓₜ (A →ₑₓₜ C))
  scompose = binaryOperatorExt $ᵣ ⱻ(_∘ₛ_) ⦃ intro(\{f₁} → s-combinator-function-function ⦃ func-f = [∨]-introₗ (⦾(binaryOperatorExt $ₗ f₁)) ⦄) ⦄

  compose : ◦((B →ₑₓₜ C) →ₑₓₜ (A →ₑₓₜ B) →ₑₓₜ (A →ₑₓₜ C))
  compose = scompose $ (constant $ scompose) $ constant

  compose₂ : ◦((B →ₑₓₜ C) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ B) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ C))
  compose₂ = compose $ compose $ compose

  compose₃ : ◦((B →ₑₓₜ C) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ B) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ C))
  compose₃ = compose $ compose $ compose₂

  compose₄ : ◦((B →ₑₓₜ C) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ A₄ →ₑₓₜ B) →ₑₓₜ (A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ A₄ →ₑₓₜ C))
  compose₄ = compose $ compose $ compose₃

  swap₂ : ◦((A →ₑₓₜ B →ₑₓₜ C) →ₑₓₜ (B →ₑₓₜ A →ₑₓₜ C))
  swap₂ = scompose $ (scompose $ (constant $ compose) $ scompose) $ (constant $ constant)

_∘₂_ : ◦(B →ₑₓₜ C) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ B) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ C)
f ∘₂ g = Internal.compose₂ $ f $ g

_∘₃_ : ◦(B →ₑₓₜ C) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ B) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ C)
f ∘₃ g = Internal.compose₃ $ f $ g

_∘₄_ : ◦(B →ₑₓₜ C) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ A₄ →ₑₓₜ B) → ◦(A₁ →ₑₓₜ A₂ →ₑₓₜ A₃ →ₑₓₜ A₄ →ₑₓₜ C)
f ∘₄ g = Internal.compose₄ $ f $ g
