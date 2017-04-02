module Numeral.Real where

import Level as Lvl
open import Functional
open import Logic(Lvl.𝟎)
open import Structure.Operator.Group(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)

data ℝ : Set where
  𝟎 : ℝ
  𝟏 : ℝ
  _+_ : ℝ → ℝ → ℝ
  _−_ : ℝ → ℝ → ℝ
  _⋅_ : ℝ → ℝ → ℝ
  _/_ : ℝ → ℝ → ℝ
  _^_ : ℝ → ℝ → ℝ
  log : ℝ → ℝ → ℝ
  _√_ : ℝ → ℝ → ℝ
  sin : ℝ → ℝ
  cos : ℝ → ℝ
  tan : ℝ → ℝ

data _<_ (_ : ℝ) (_ : ℝ) : Stmt where

postulate Axiom1 : Group {ℝ} (_+_) 𝟎 (𝟎 −_)
postulate Axiom2 : Group {ℝ} (_⋅_) 𝟏 (𝟏 /_)
postulate Axiom3ₗ : Distributivityₗ {ℝ} {ℝ} (_⋅_) (_+_)
postulate Axiom3ᵣ : Distributivityᵣ {ℝ} {ℝ} (_⋅_) (_+_)

-- postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
-- postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(y ↦ (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ≡ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(z ↦ (x + z) ≡ y)
