module Syntax.Implication.Dependent where

open import Functional using (id)
open import Functional.Dependent
import      Lvl
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

_⇒-[_]_ : ∀(X : Type{ℓ₁}){Y : ∀{_ : X} → Type{ℓ₂}}{Z : ∀{x : X}{_ : Y{x}} → Type{ℓ₃}} → (P : (x : X) → Y{x}) → (∀{x : X} → (y : Y{x}) → Z{x}{y}) → ((x : X) → Z{x}{P(x)})
_⇒-[_]_ = const(swap(_∘_))
infixr 0.98 _⇒-[_]_
{-# INLINE _⇒-[_]_ #-}

_⇒-[]_ : ∀(X : Type{ℓ₁}){Y : ∀{_ : X} → Type{ℓ₂}} → ((x : X) → Y{x}) → ((x : X) → Y{x})
_⇒-[]_ = const id
infixr 0.98 _⇒-[]_
{-# INLINE _⇒-[]_ #-}

_⇒-end : ∀(X : Type{ℓ₁}) → (X → X)
_⇒-end = const id
infixr 0.99 _⇒-end
{-# INLINE _⇒-end #-}

_⇒_ = apply
infixl 0.97 _⇒_
{-# INLINE _⇒_ #-}

•_•_⇒₂_ : ∀{X : Type{ℓ₁}}{Y : ∀{_ : X} → Type{ℓ₂}}{Z : ∀{x : X}{_ : Y{x}} → Type{ℓ₃}} → (x : X) → (y : Y{x}) → ((x : X) → (y : Y{x}) → Z{x}{y}) → Z{x}{y}
• a • b ⇒₂ P = P ⇒ apply a ⇒ apply b
infixl 0.97 •_•_⇒₂_
{-# INLINE •_•_⇒₂_ #-}