module Data.Option.Relation where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Data.Option
open import Data.Option.Functions
open import Functional
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}

IsSome : Option(T) → Type
IsSome = IsTrue ∘ isSome

IsNone : Option(T) → Type
IsNone = IsTrue ∘ isNone

Matching : (A → B → Type{ℓ}) → (Option(A) → Option(B) → Type{ℓ})
Matching(_▫_) None     None     = Unit
Matching(_▫_) None     (Some y) = Empty
Matching(_▫_) (Some x) None     = Empty
Matching(_▫_) (Some x) (Some y) = x ▫ y
