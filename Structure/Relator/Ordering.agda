module Structure.Relator.Ordering {l₁} {l₂} where

import      Level as Lvl
open import Data
open import Functional
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Logic.Theorems{l₁ Lvl.⊔ l₂}
open import Structure.Relator.Properties{l₁}{l₂}
open import Type{l₂}

record WeakPartialOrder {T : Type} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    reflexivity  : Reflexivity  (_≤_)

record StrictPartialOrder {T : Type} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry  : Antisymmetry  (_≤_) (_≡_)
    transitivity  : Transitivity  (_≤_)
    irreflexivity : Irreflexivity (_≤_)

record StrictOrder {T : Type} (_<_ : T → T → Stmt) : Stmt where
  field
    asymmetry     : Asymmetry     (_<_)
    transitivity  : Transitivity  (_<_)
    irreflexivity : Irreflexivity (_<_)

-- StrictOrder-asymmetry : {T : _}{_<_ : _} → StrictOrder (_<_) → Asymmetry (_<_)
-- StrictOrder-asymmetry ordering {x} {y} (x<y) =
--   (StrictOrder.transitivity ordering)(
--     (Tuple.uncurry
--       (swap
--         ([⊥]-elim ∘ (StrictOrder.irreflexivity ordering))
--       )
--     )
--   )
-- ∀x. ¬(x<x) //StrictOrder.irreflexivity ordering
-- ∀x. (x<x) → ⊥ //Definition: (¬)
-- ∀x. (x<x) → ¬(y<x) //[⊥]-elim
-- ∀x. (x<x) → (y<x) → ⊥ //Definition: (¬)
-- ∀x. (y<x) → (x<x) → ⊥ //swap (..)
-- ∀x. (y<x) ∧ (x<x) → ⊥ //Tuple.uncurry
-- ∀x. (y<x) → ⊥ //Nope

Minimum : {T : Type} → (T → T → Stmt) → T → Stmt
Minimum {T} (_≤_) min = ∀{x : T} → (min ≤ x)

Maximum : {T : Type} → (T → T → Stmt) → T → Stmt
Maximum {T} (_≤_) max = ∀{x : T} → (x ≤ max)
