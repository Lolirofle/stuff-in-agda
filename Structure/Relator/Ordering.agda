module Structure.Relator.Ordering {l₁} {l₂} where

import      Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Predicate{l₁}{l₂}
open import Logic.Theorems{l₁ Lvl.⊔ l₂}
open import Structure.Relator.Properties{l₁}{l₂}
open import Type{l₂}

record WeakPartialOrder {T : Type} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    reflexivity  : Reflexivity  (_≤_)

record TotalWeakPartialOrder {T : Type} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    weakPartialOrder : WeakPartialOrder (_≤_) (_≡_)
    totality         : Total (_≤_)

record StrictPartialOrder {T : Type} (_<_ : T → T → Stmt) : Stmt where
  field
    transitivity  : Transitivity  (_<_)
    asymmetry     : Asymmetry     (_<_)
    irreflexivity : Irreflexivity (_<_)

Minimum : {T : Type} → (T → T → Stmt) → T → Stmt
Minimum {T} (_≤_) min = ∀{x : T} → (min ≤ x)

Maximum : {T : Type} → (T → T → Stmt) → T → Stmt
Maximum {T} (_≤_) max = ∀{x : T} → (x ≤ max)

Dense : {T : Type} → (T → T → Stmt) → Stmt
Dense {T} (_<_) = ∀{x y : T} → (x < y) → ∃(z ↦ (x < z)∧(z < y))
