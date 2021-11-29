module Type.Properties.MereProposition {ℓ ℓₑ} where

import      Lvl
open import Functional.Instance
open import Structure.Setoid
open import Type

-- A type is a mere proposition type when there is at most one inhabitant (there is at most one object with this type).
-- In other words: If there is an inhabitant of type T, it is unique (essentially only allowing empty or singleton types, but this is not provable (excluded middöe)).
-- Also called:
-- • "Irrelevance" / "Irrelevancy" / "Proof irrelevance" (in the context of proofs).
--   A proof of the proposition T is unique (using equality to determine uniqueness).
-- • "isProp" / "h-proposition" / "is of h-level 1" / "a mere proposition" (in homotopy type theory).
--   Classically, when MereProposition(T), T is either empty or a singleton (which in the context of proofs corresponds to types isomorphic to ⊥ or ⊤).
-- • "subsingleton" (in set theory)
--   When a type and its inhabitants is interpreted as a set and its elements.
-- • "subterminal object" (in category theory).
module _ (T : Type{ℓ}) ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
  record MereProposition : Type{ℓ Lvl.⊔ ℓₑ} where
    constructor intro
    field uniqueness : ∀{x y : T} → (x ≡ y)
  uniqueness = inferArg MereProposition.uniqueness

-- TODO: Consider using unicode ◐○●⧭⦵⦳
