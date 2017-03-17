module Numeral.Real where

import Level as Lvl
open import Logic(Lvl.𝟎)

data ℝ : Set where

data _≡_ (_ : ℝ) (_ : ℝ) : Stmt where

data _<_ (_ : ℝ) (_ : ℝ) : Stmt where

-- data _+_ (_ : ℝ) (_ : ℝ) : ℝ where

postulate 𝟎 : ℝ
postulate Axiom1 : {x y : ℝ} → (x < y) → ¬ (y < x)
postulate Axiom2 : {x z : ℝ} → (x < z) → ∃(λ y → (x < y) ∧ (y < z))
-- postulate Axiom4 : {x y z : ℝ} → ((x + y) + z) ↔ (x + (y + z))
-- postulate Axiom5 : {x y : ℝ} → ∃(λ z → (x + z) ≡ y)
