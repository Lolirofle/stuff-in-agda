module Structure.Relator.Properties lvl where

open import Logic(lvl)
open import Numeral.Natural
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
-- transitivityChain {T} (_▫_) = {X : (NonEmptyList.List 1 T)} → (NonEmptyList.reduceₗ (_∧_) (NonEmptyList.fromList (NonEmptyList.mapWindow2ₗ (_▫_) X) ⊥)) → ((NonEmptyList.firstElem X) ▫ (NonEmptyList.lastElem X))
transitivityChain : ∀ {n} → {T : Set n} → (T → T → Stmt) → {_ : NonEmptyList.List 1 T} → Stmt
transitivityChain {T} (_▫_) {X} = (NonEmptyList.reduceₗ (_∧_) (NonEmptyList.fromList (NonEmptyList.mapWindow2ₗ (_▫_) X) ⊥)) → ((NonEmptyList.firstElem X) ▫ (NonEmptyList.lastElem X))

testType : {_▫_ : ℕ → ℕ → Stmt} → transitivityChain _▫_ {1 NonEmptyList.⤙ 2 NonEmptyList.⤙  3 NonEmptyList.⤙ (NonEmptyList.End 4)} → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
testType x = x

-- transitivityChain {T} (_▫_) X = (NonEmptyList.fromList (NonEmptyList.mapWindow2ₗ (_▫_) X) ⊥)
-- 
-- testType : {_▫_ : ℕ → ℕ → Stmt} → transitivityChain _▫_ (1 NonEmptyList.⤙ 2 NonEmptyList.⤙ (NonEmptyList.End 3)) → ((1 ▫ 2) NonEmptyList.⤙ (NonEmptyList.End(2 ▫ 3)))
-- testType x = x
