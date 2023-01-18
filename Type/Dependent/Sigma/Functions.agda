-- Compared to Type.Dependent.Functions, this module uses the dependent function type as Π.
module Type.Dependent.Sigma.Functions where

import      Lvl
open import DependentFunctional
open import Type
open import Type.Dependent.PiFunction
open import Type.Dependent.Sigma using (Σ ; intro)
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

module _
  {A : Type{ℓ₁}}
  {B : A → Type{ℓ₂}}
  {C : Σ A B → Type{ℓ₃}}
  where

  elim : ((a : A) → (b : B(a)) → C(intro a b)) → ((s : Σ A B) → C(s))
  elim f(intro a b) = f a b

module _
  {A : Type{ℓ₁}}
  {B : A → Type{ℓ₂}}
  {C : ∀{a : A} → B(a) → Type{ℓ₃}}
  where

  curry : (Π(Σ A B) (C ∘ Σ.right)) → (Π A (a ↦ (Π(B(a)) C)))
  curry = _∘₂ intro

  uncurry : (Π A (a ↦ Π(B(a)) C)) → (Π(Σ A B) (C ∘ Σ.right))
  uncurry f(intro a b) = f a b
