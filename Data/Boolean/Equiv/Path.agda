{-# OPTIONS --cubical #-}

module Data.Boolean.Equiv.Path where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Structure.Relator.Properties
open import Structure.Relator
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path.Properties
open import Type.Identity

Bool-different-values : ¬(Path 𝐹 𝑇)
Bool-different-values p = substitute₁ₗ(IsTrue) p <>

instance
  Bool-identityPath : IdentityPathType(Bool)
  _⊆₂_.proof Bool-identityPath {𝑇} {𝑇} _ = intro
  _⊆₂_.proof Bool-identityPath {𝑇} {𝐹}   = [⊥]-elim ∘ Bool-different-values ∘ symmetry(Path)
  _⊆₂_.proof Bool-identityPath {𝐹} {𝑇}   = [⊥]-elim ∘ Bool-different-values
  _⊆₂_.proof Bool-identityPath {𝐹} {𝐹} _ = intro
