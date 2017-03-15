module Structure.Relator.Properties lvl where

open import Logic(lvl)
import List
import NonEmptyList

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

Areflexivity : {T : Stmt} → (T → T → Stmt) → Stmt
Areflexivity {T} (_▫_) = {x : T} → ¬(x ▫ x)



-- TODO: For constructions/proofs of this form: Proof of a=f: a=b ∧ b=c ∧ c=d ∧ d=e ∧ e=f (also expressed as a=b=c=d=e=f)
-- transitivityChain : {T : Stmt} → (T → T → Stmt) → Stmt
-- transitivityChain {T} (_▫_) = {X : (List.List T)} → (List.reduceₗ (_∧_) ((NonEmptyList.mapWindow2ₗ (_▫_) X) List.or (List.singleton ⊥))) → ((NonEmptyList.firstElem X) ▫ (NonEmptyList.lastElem X))
