module Structure.Equivalence where

open import Logic
open import LogicTheorems

Reflexivity : {T : Set} → (T → T → Set) → Set
Reflexivity {T} (_▫_) = {x : T} → (x ▫ x)

Symmetry : {T : Set} → (T → T → Set) → Set
Symmetry {T} (_▫_) = {x y : T} → (x ▫ y) → (y ▫ x)

Transitivity : {T : Set} → (T → T → Set) → Set
Transitivity {T} (_▫_) = {x y z : T} → (x ▫ y) → (y ▫ z) → (x ▫ z)

record Equivalence {T : Set} (_▫_ : T → T → Set) : Set where
  field
    reflexivity  : Reflexivity  (_▫_)
    symmetry     : Symmetry     (_▫_)
    transitivity : Transitivity (_▫_)

-- Equals
infixl 15 _≡_
data _≡_ {T : Set} : T -> T -> Set where
  reflexivity : {x : T} -> (x ≡ x)

[≡]-reflexivity : {T : Set} → Reflexivity {T} (_≡_ {T})
[≡]-reflexivity = reflexivity

[≡]-symmetry : {T : Set} → Symmetry {T} (_≡_ {T})
[≡]-symmetry reflexivity = reflexivity -- TODO: How does this work?

[≡]-transitivity : {T : Set} → Transitivity {T} (_≡_ {T})
[≡]-transitivity reflexivity reflexivity = reflexivity -- TODO: Or even this? But maybe I can ignore it for now

[≡]-equivalence : {T : Set} → Equivalence {T} (_≡_ {T})
[≡]-equivalence = record {
    reflexivity  = [≡]-reflexivity ;
    symmetry     = [≡]-symmetry    ;
    transitivity = [≡]-transitivity
  }

Commutativity : {T : Set} → (T → T → T) → Set
Commutativity {T} (_▫_) = {x y : T} → (x ▫ y) ≡ (y ▫ x)

Associativity : {T : Set} → (T → T → T) → Set
Associativity {T} (_▫_) = {x y z : T} → ((x ▫ y) ▫ z) ≡ ((x ▫ y) ▫ z)

Identityₗ : {T : Set} → (T → T → T) → T → Set
Identityₗ {T} (_▫_) id = {x : T} → (id ▫ x) ≡ x -- TODO: id should be existential? How to express

Identityᵣ : {T : Set} → (T → T → T) → T → Set
Identityᵣ {T} (_▫_) id = {x : T} → (x ▫ id) ≡ x

Inverseₗ : {T : Set} → (T → T → T) → T → (T → T) → Set
Inverseₗ {T} (_▫_) id inv = {x : T} → ((inv x) ▫ x) ≡ id

Inverseᵣ : {T : Set} → (T → T → T) → T → (T → T) → Set
Inverseᵣ {T} (_▫_) id inv = {x : T} → (x ▫ (inv x)) ≡ id

record Group {T : Set} (_▫_ : T → T → T) (id : T) (inv : T → T) : Set where
  field
    commutativity  : Commutativity  (_▫_)
    associativity  : Associativity  (_▫_)
    identity       : Identityₗ       (_▫_) id
    inverse        : Inverseₗ        (_▫_) id inv

Group-inverseᵣ : {T : Set} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Inverseᵣ {T} (_▫_) id inv)
Group-inverseᵣ group = [≡]-transitivity (Group.commutativity group) (Group.inverse group)

Group-identityᵣ : {T : Set} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Identityᵣ {T} (_▫_) id)
Group-identityᵣ group = [≡]-transitivity (Group.commutativity group) (Group.identity group)

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

