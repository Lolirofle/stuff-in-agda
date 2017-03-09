module Structure.Equivalence where

open import Logic
open import LogicTheorems

-- record EquivalenceRelation (_≡_ : Set → Set → Set) : Set₁ where
--   field
--     reflexivity  : (x : Set) → (x ≡ x)
--     symmetry     : (x y : Set) → (x ≡ y) → (y ≡ x)
--     transitivity : (x y z : Set) → (x ≡ y) → (y ≡ z) → (x ≡ z)

-- record PartialOrder {T : _} (_≤_ : T → T → Stmt) (_≡_ : T → T → Stmt) : Set where
--   field
--     antisymmetry : {a b : T} → ((a ≤ b) ∧ (b ≤ a)) → (a ≡ b)
--     transitivity : {a b c : T} → ((a ≤ b) ∧ (b ≤ c)) → (a < c)
--     reflexivity  : {a : T} → (a ≤ a)

-- record StrictOrder {T : _} (_<_ : T → T → Stmt) : Set where
--   field
--     areflexivity : {a : T} → ¬ (a < a)
--     transitivity : {a b c : T} → ((a < b) ∧ (b < c)) → (a < c)

-- StrictOrder-asymmetry : {T : _} → {_<_ : _} → StrictOrder (_<_) → ({a b : T} → (a < b) → ¬ (b < a))
-- StrictOrder-asymmetry ordering {a} {b} (a<b) =
--   [→]-syllogism (StrictOrder.transitivity ordering {a} {b} {a}) (StrictOrder.areflexivity ordering {a})

