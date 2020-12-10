module Data.List.Relation.Quantification where

import      Lvl
open import Data.List
open import Logic
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable x y : T
private variable P : T → Stmt{ℓ}

data AllElements (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  ∅ : AllElements(P)(∅)
  _⊰_ : P(x) → AllElements(P)(l) → AllElements(P)(x ⊰ l)

data ExistsElement (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  •_ : P(x) → ExistsElement(P)(x ⊰ l)
  ⊰_ : ExistsElement(P)(l) → ExistsElement(P)(x ⊰ l)

data AllElements₂ (P : A → B → Stmt{ℓ}) : List(A) → List(B) → Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓ} where
  ∅ : AllElements₂(P)(∅)(∅)
  _⊰_ : P(x)(y) → AllElements₂(P)(l₁)(l₂) → AllElements₂(P)(x ⊰ l₁)(y ⊰ l₂)
