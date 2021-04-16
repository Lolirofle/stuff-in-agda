{-# OPTIONS --cubical #-}

module Data.Boolean.Equiv.Path where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Structure.Relator.Properties
open import Structure.Relator
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path
open import Type.Identity

Bool-different-values : ¬(Path 𝐹 𝑇)
Bool-different-values p = substitute₁ₗ(IsTrue) p <>

Bool-Path-to-Id : ∀{x y : Bool} → (Path x y) → (Id x y)
Bool-Path-to-Id {𝑇} {𝑇} _ = intro
Bool-Path-to-Id {𝑇} {𝐹}   = [⊥]-elim ∘ Bool-different-values ∘ symmetry(Path)
Bool-Path-to-Id {𝐹} {𝑇}   = [⊥]-elim ∘ Bool-different-values
Bool-Path-to-Id {𝐹} {𝐹} _ = intro
