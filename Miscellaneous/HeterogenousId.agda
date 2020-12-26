module Miscellaneous.HeterogenousId where

import      Lvl
open import Logic
open import Logic.Propositional
open import Functional
open import Type

-- TODO: Will this work for getting function extensionality? Probably not?
data IdFn {ℓ} : ∀{T : Type{ℓ}} → T → T → Stmt{Lvl.𝐒(ℓ)} where
  IdFn-intro : ∀{T}{x : T} → (IdFn x x)
  IdFn-func : ∀{A B : Type{ℓ}}{f g : A → B} → (∀{x : A} → IdFn(f(x))(g(x))) → (IdFn f g)
