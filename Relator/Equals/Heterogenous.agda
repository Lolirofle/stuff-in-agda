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

-- TODO: Why is this not a very simple solution to not having function extensionality?
data IdFn {ℓ} : ∀{T : Type{ℓ}} → T → T → Stmt{Lvl.𝐒(ℓ)} where
  IdFn-intro : ∀{T}{x : T} → (IdFn x x)
  IdFn-func : ∀{A B : Type{ℓ}}{f g : A → B} → (∀{x : A} → IdFn(f(x))(g(x))) → (IdFn f f)
