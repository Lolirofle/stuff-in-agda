module Structure.Relator.Ordering lvl where

open import Logic(lvl)
open import LogicTheorems(lvl)
open import Structure.Relator.Properties(lvl)

record PartialOrder {T : Stmt} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Stmt where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    reflexivity  : Reflexivity  (_≤_)

record StrictOrder {T : Stmt} (_<_ : T → T → Stmt) : Stmt where
  field
    areflexivity : Areflexivity (_<_)
    transitivity : Transitivity (_<_)

-- StrictOrder-asymmetry : {T : _} → {_<_ : _} → StrictOrder (_<_) → Asymmetry (_<_)
-- StrictOrder-asymmetry ordering =
--   [→]-syllogism (StrictOrder.transitivity ordering) (StrictOrder.areflexivity ordering)
