module Type.Unit {ℓ} where

import      Lvl
open import Sets.Setoid
open import Type

-- A type is an unit type when it has exactly one inhabitant (there is only one object with this type).
-- In other words: There is an unique inhabitant of type T.
-- IsUnit(T) is sometimes also called "T is a singleton", or "T is contractible".
record IsUnit (T : Type{ℓ}) ⦃ _ : Equiv(T) ⦄ : Type{ℓ} where
  constructor intro
  field
    unit : T
    uniqueness : ∀{x : T} → (x ≡ unit)

-- A type is a mere proposition type when there is at most one inhabitant (there is at most one object with this type).
-- In other words: If there is an inhabitant of type T, it is unique.
-- In the context of proofs:
--   Also called "Irrelevance", "Irrelevancy" or "Proofs Irrelevance".
--   A proof of the proposition T is unique (using equality to determine uniqueness).
-- In homotopy type theory, this is called:
-- • "isProp"
-- • "is of h-level 1"
-- • "a mere proposition"
-- Classically, when IsProp(T), T is either empty or a singleton (which in the context of proofs corresponds to ⊥ and ⊤).
record IsProp (T : Type{ℓ}) ⦃ _ : Equiv(T) ⦄ : Type{ℓ} where
  constructor intro
  field
    uniqueness : ∀{x y : T} → (x ≡ y)
