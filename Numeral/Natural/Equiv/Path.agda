{-# OPTIONS --cubical #-}

module Numeral.Natural.Equiv.Path where

open import Data.Boolean.Equiv.Path
open import Functional
open import Logic.Propositional
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural
open import Relator.Equals.Proofs.Equivalence using () renaming ([≡]-equiv to Id-equiv ; [≡]-symmetry to Id-symmetry ; [≡]-to-function to Id-to-function ; [≡]-function to Id-function)
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path
open import Type.Identity

instance
  𝐒-injective : Injective(𝐒)
  Injective.proof 𝐒-injective p = congruence₁(𝐏) p

ℕ-Path-to-Id : ∀{x y : ℕ} → (Path x y) → (Id x y)
ℕ-Path-to-Id {𝟎}   {𝟎}   p = intro
ℕ-Path-to-Id {𝟎}   {𝐒 y}   = [⊥]-elim ∘ Bool-different-values ∘ congruence₁(positive?)
ℕ-Path-to-Id {𝐒 x} {𝟎}     = [⊥]-elim ∘ Bool-different-values ∘ symmetry(Path) ∘ congruence₁(positive?)
ℕ-Path-to-Id {𝐒 x} {𝐒 y} p = congruence₁ ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (ℕ.𝐒) ⦃ Id-function ⦄ (ℕ-Path-to-Id {x}{y} (injective(ℕ.𝐒) p))
