{-# OPTIONS --cubical #-}

module Data.Boolean.Equiv.Path where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Logic.Propositional
open import Structure.Relator
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality

Bool-different-values : ¬(Path 𝐹 𝑇)
Bool-different-values p = substitute₁ₗ(IsTrue) p <>
