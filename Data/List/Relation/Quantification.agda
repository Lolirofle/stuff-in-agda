module Data.List.Relation.Quantification where

import      Lvl
open import Data.List
open import Logic
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l : List(T)
private variable x : T

data AllElements (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  ∅ : AllElements(P)(∅)
  _⊰_ : P(x) → AllElements(P)(l) → AllElements(P)(x ⊰ l)

data ExistsElement (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  •_ : P(x) → ExistsElement(P)(x ⊰ l)
  ⊰_ : ExistsElement(P)(l) → ExistsElement(P)(x ⊰ l)
