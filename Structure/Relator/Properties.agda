module Structure.Relator.Properties lvl where

open import Logic(lvl)
open import Numeral.Natural
open import NonEmptyList as List
  using (List ; _⤙_ ; _⤛_ ; End)

Reflexivity : {T : Stmt} → (T → T → Stmt) → Stmt
Reflexivity {T} (_▫_) = {x : T} → (x ▫ x)

Symmetry : {T : Stmt} → (T → T → Stmt) → Stmt
Symmetry {T} (_▫_) = {x y : T} → (x ▫ y) → (y ▫ x)

Transitivity : {T : Stmt} → (T → T → Stmt) → Stmt
Transitivity {T} (_▫_) = {x y z : T} → ((x ▫ y) ∧ (y ▫ z)) → (x ▫ z)

Antisymmetry : {T : Stmt} → (T → T → Stmt) → (T → T → Stmt) → Stmt
Antisymmetry {T} (_▫₁_) (_▫₂_) = {a b : T} → ((a ▫₁ b) ∧ (b ▫₁ a)) → (a ▫₂ b)

Asymmetry : {T : Stmt} → (T → T → Stmt) → Stmt
Asymmetry {T} (_▫_) = {x y : T} → (x ▫ y) → ¬(y ▫ x)

Irreflexivity : {T : Stmt} → (T → T → Stmt) → Stmt
Irreflexivity {T} (_▫_) = {x : T} → ¬(x ▫ x)

Total : {T : Stmt} → (T → T → Stmt) → Stmt
Total {T} (_▫_) = {x y : T} → (x ▫ y) ∨ (y ▫ x)

-- Dichotomy : {T : Stmt} → (T → T → Stmt) → Stmt
-- Dichotomy {T} (_▫_) = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

-- Trichotomy : {T : Stmt} → (T → T → Stmt) → Stmt
-- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them

-- For constructions/proofs of this form: Proof of a=f: a=b ∧ b=c ∧ c=d ∧ d=e ∧ e=f (also expressed as a=b=c=d=e=f)
TransitivityChain : ∀ {n} → {T : Set n} → (T → T → Stmt) → (List 1 T) → Stmt
TransitivityChain {T} (_▫_) X = (List.reduceₗ (_∧_) (List.fromList (List.mapWindow2ₗ (_▫_) X) ⊥)) → ((List.firstElem X) ▫ (List.lastElem X))

-- TODO
-- transitivityChain : TransitivityChain 
-- transitivityChain  = 

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → transitivityChain _▫_ (1 ⤙ 2 ⤙ 3 ⤛ 4) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain x = x
