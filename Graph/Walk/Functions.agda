open import Type

module Graph.Walk.Functions {ℓ₁ ℓ₂} {V : Type{ℓ₁}} where

import      Lvl
open import Graph{ℓ₁}{ℓ₂}(V)
open import Graph.Properties
open import Graph.Walk{ℓ₁}{ℓ₂}{V}
open import Numeral.Natural
open import Syntax.Function
open import Type.Dependent
open import Type.Dependent.Functions

module _ {_⟶_ : Graph} where
  edge : ∀{a b} → (a ⟶ b) → (Walk(_⟶_) a b)
  edge e = prepend e at

  join : ∀{a b c} → (a ⟶ b) → (b ⟶ c) → (Walk(_⟶_) a c)
  join e₁ e₂ = prepend e₁ (edge e₂)

  _++_ : ∀{a b c} → Walk(_⟶_) a b → Walk(_⟶_) b c → Walk(_⟶_) a c
  at            ++ w₂ = w₂
  prepend e₁ w₁ ++ w₂ = prepend e₁ (w₁ ++ w₂)

  postpend : ∀{a b c} → (Walk(_⟶_) a b) → (b ⟶ c) → (Walk(_⟶_) a c)
  postpend at             e₂ = edge e₂
  postpend (prepend e₁ w) e₂ = prepend e₁ (postpend w e₂)

  reverse : ⦃ Undirected(_⟶_) ⦄ → ∀{a b} → Walk(_⟶_) a b → Walk(_⟶_) b a
  reverse at            = at
  reverse (prepend e w) = postpend (reverse w) (undirected-reverse(_⟶_) e)

  prelop : ∀{a c} → (Walk(_⟶_) a c) → Σ(_)(b ↦ Walk(_⟶_) b c)
  prelop at            = intro _ at
  prelop (prepend e w) = intro _ w

  -- TODO: Terminated before but not on Agda version 2.6.2-9bed10c
  {-# TERMINATING #-}
  postlop : ∀{a c} → (Walk(_⟶_) a c) → Σ(_)(b ↦ Walk(_⟶_) a b)
  postlop at                          = intro _ at
  postlop (prepend e  at)             = intro _ at
  postlop (prepend e₁ (prepend e₂ w)) = [Σ]-applyᵣ (postlop(prepend e₂ w)) (prepend e₁)

  length : ∀{a b} → (Walk(_⟶_) a b) → ℕ
  length at            = 𝟎
  length (prepend _ w) = 𝐒(length w)
