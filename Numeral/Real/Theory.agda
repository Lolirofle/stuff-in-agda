module Numeral.Real.Theory where

import      Level as Lvl
open import Structure.Operator.Field {Lvl.𝟎}{Lvl.𝟎}

record [ℝ]-sym (R : Set) : Set where
  field
    𝟎 : R
    𝟏 : R
    _+_ : R → R → R
    _⋅_ : R → R → R
    _≤_ : R → R → Set

module [ℝ]-symbols where
  open [ℝ]-sym {{...}}

-- Theory defining the axioms of ℝ
record [ℝ]-theory {R : Set} (sym : [ℝ]-sym(R)) : Set where
  field
    [+][⋅]-field      : Field(R)(_+_)(_⋅_)
    [≤]-totalOrder    : TotalOrder(R)(_≤_)
    [+][≤]-preserve   : ∀{x y} → (x ≤ y) → ∀{z} → ((x + z) ≤ (y + z))
    [⋅][≤]-preserve   : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (y + z))
    dedekind-complete : ∀{Rₛ}{subset : R → Rₛ} → UpperBounded(subset) → Infimumed(subset)
