module Structure.Relator.Ordering lvl where

open import Logic(lvl)
open import LogicTheorems(lvl)
open import Structure.Relator.Properties(lvl)

record PartialOrder {T : Set} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    irreflexivity  : Irreflexivity  (_≤_)

record StrictOrder {T : Set} (_<_ : T → T → Stmt) : Stmt where
  field
    irreflexivity : Irreflexivity (_<_)
    transitivity : Transitivity (_<_)

-- StrictOrder-asymmetry : {T : _} → {_<_ : _} → StrictOrder (_<_) → Asymmetry (_<_)
-- StrictOrder-asymmetry ordering =
--   [→]-syllogism (StrictOrder.transitivity ordering) (StrictOrder.areflexivity ordering)
