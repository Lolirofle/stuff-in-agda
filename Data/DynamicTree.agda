module Data.DynamicTree where

import      Lvl
open import Data.List
open import Data.Option
open import Functional as Fn
open import Type

private variable ℓ ℓᵢ : Lvl.Level
private variable T A B : Type{ℓ}

data Node (T : Type{ℓ}) : Type{ℓ} where
  node : T → List(Node(T)) → Node(T)

DynamicTree : Type{ℓ} → Type{ℓ}
DynamicTree(T) = Option(Node(T))
