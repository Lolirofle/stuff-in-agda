module Relator.Equals.Heterogenous where

import      Lvl
open import Logic
open import Logic.Propositional
open import Functional
open import Type

infixl 15 _≡_

data _≡_ {ℓ} : ∀{A : Type{ℓ}}{B : Type{ℓ}} → A → B → Stmt{Lvl.𝐒(ℓ)} where
  instance [≡]-intro : ∀{T : Type{ℓ}}{x : T} → (x ≡ x)

module _ {ℓ}{A B : Type{ℓ}}where
  infixl 15 _≢_

  _≢_ : A → B → Stmt{Lvl.𝐒(ℓ)}
  _≢_ a b = ¬(a ≡ b)

  [≡]-type : ∀{x : A}{y : B} → (x ≡ y) → (A ≡ B)
  [≡]-type [≡]-intro = [≡]-intro
