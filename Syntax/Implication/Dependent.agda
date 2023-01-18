module Syntax.Implication.Dependent where

open import Functional using (id)
open import DependentFunctional
import      Lvl
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level

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

-- TODO: Change these to be similar to the ones in Syntax.Implication
•_⇒₁_ = apply
infixl 0.97 •_⇒₁_
{-# INLINE •_⇒₁_ #-}

•_•_⇒₂_ : ∀{X : Type{ℓ₁}}{Y : ∀{_ : X} → Type{ℓ₂}}{Z : ∀{x : X}{_ : Y{x}} → Type{ℓ₃}} → (x : X) → (y : Y{x}) → ((x : X) → (y : Y{x}) → Z{x}{y}) → Z{x}{y}
• a • b ⇒₂ P = P ⇒ apply a ⇒ apply b
infixl 0.97 •_•_⇒₂_
{-# INLINE •_•_⇒₂_ #-}

•_•_•_⇒₃_ : ∀{X : Type{ℓ₁}}{Y : ∀{_ : X} → Type{ℓ₂}}{Z : ∀{x : X}{_ : Y{x}} → Type{ℓ₃}}{W : ∀{x : X}{y : Y{x}}{_ : Z{x}{y}} → Type{ℓ₄}} → (x : X) → (y : Y{x}) → (z : Z{x}{y}) → ((x : X) → (y : Y{x}) → (z : Z{x}{y}) → W{x}{y}{z}) → W{x}{y}{z}
• a • b • c ⇒₃ P = P ⇒ apply a ⇒ apply b ⇒ apply c
infixl 0.97 •_•_•_⇒₃_
{-# INLINE •_•_•_⇒₃_ #-}
