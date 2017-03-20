module Structure.Relator.Ordering lvl where

open import Data
open import Functional
open import Logic(lvl)
open import LogicTheorems(lvl)
open import Structure.Relator.Properties(lvl)

record WeakPartialOrder {T : Set} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    reflexivity  : Reflexivity  (_≤_)

record StrictPartialOrder {T : Set} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry  : Antisymmetry  (_≤_) (_≡_)
    transitivity  : Transitivity  (_≤_)
    irreflexivity : Irreflexivity (_≤_)

record StrictOrder {T : Set} (_<_ : T → T → Stmt) : Stmt where
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
