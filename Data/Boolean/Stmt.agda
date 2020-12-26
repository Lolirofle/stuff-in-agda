module Data.Boolean.Stmt where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Logic.Propositional
open import Type

IsTrue : Bool → Type
IsTrue = if_then ⊤ else ⊥

IsFalse : Bool → Type
IsFalse = IsTrue ∘ !
