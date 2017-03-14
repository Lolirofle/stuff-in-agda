module Structure.Relator.Ordering where

open import Logic
open import LogicTheorems
open import Structure.Relator.Properties

record PartialOrder {T : Set} (_≤_ : T → T → Set) (_≡_ : T → T → Set) : Set where
  field
    antisymmetry : Antisymmetry (_≤_) (_≡_)
    transitivity : Transitivity (_≤_)
    reflexivity  : Reflexivity  (_≤_)

record StrictOrder {T : Set} (_<_ : T → T → Set) : Set where
  field
    areflexivity : Areflexivity (_<_)
    transitivity : Transitivity (_<_)

-- StrictOrder-asymmetry : {T : _} → {_<_ : _} → StrictOrder (_<_) → Asymmetry (_<_)
-- StrictOrder-asymmetry ordering =
--   [→]-syllogism (StrictOrder.transitivity ordering) (StrictOrder.areflexivity ordering)
