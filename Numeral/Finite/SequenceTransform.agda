module Numeral.Finite.SequenceTransform where

open import Functional
open import Numeral.Finite
open import Numeral.Finite.Oper
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Relation as ℕ

-- Shifts all arguments and values of the given mapping up by one and adds (0 ↦ 0).
-- The point of this function is to be able to construct a mapping that preserves injectivity and surjectivity while increasing the domain and codomain by a single value.
-- Examples:
--   prependIdMap \{0 → 3 ; 1 → 4 ; 2 → 1 ; 3 → 2 ; 4 → 0}
--   ⊜    \{0 → 0 ; 1 → 4 ; 2 → 5 ; 3 → 2 ; 4 → 3 ; 5 → 1}
--
--   prependIdMap \{0 → a    ; 1 → b    ; 2 → c    ; 3 → d    ; 4 → e}
--   ⊜    \{0 → 0 ; 1 → 𝐒(a) ; 2 → 𝐒(b) ; 3 → 𝐒(c) ; 4 → 𝐒(d) ; 5 → 𝐒(e)}
prependIdMap : ∀{a b} → (𝕟(a) → 𝕟(b)) → (𝕟(𝐒(a)) → 𝕟(𝐒(b)))
prependIdMap f(𝟎)    = 𝟎
prependIdMap f(𝐒(n)) = 𝐒(f(n))

prependIdMaps : (n : ℕ) → ∀{a b} → (𝕟(a) → 𝕟(b)) → (𝕟(a ℕ.+ n) → 𝕟(b ℕ.+ n))
prependIdMaps 𝟎     = id
prependIdMaps (𝐒 n) = prependIdMaps n ∘ prependIdMap

-- Shifts all arguments some of the values of the given mapping down by one and removes the mapping that 0 is mapped to.
-- The point of this function is to be able to construct a mapping that preserves injectivity and surjectivity while shrinking the domain and codomain by a single value.
-- Examples:
--   popShiftMap \{0 → 0 ; 1 → 1 ; 2 → 2 ; 3 → 3 ; 4 → 4}
--   ⊜                  \{0 → 0 ; 1 → 1 ; 2 → 2 ; 3 → 3}
--   popShiftMap \{0 → 4 ; 1 → 3 ; 2 → 2 ; 3 → 1 ; 4 → 0}
--   ⊜                   \{0 → 3 ; 1 → 2 ; 2 → 1 ; 3 → 0}
--   popShiftMap \{0 → 3 ; 1 → 4 ; 2 → 1 ; 3 → 2 ; 4 → 0 ; 5 → 6 ; 6 → 5}
--   ⊜                   \{0 → 3 ; 1 → 1 ; 2 → 2 ; 3 → 0 ; 4 → 5 ; 5 → 4}
popShiftMap : ∀{a b} ⦃ pos : ℕ.Positive(b) ⦄ → (𝕟(a) → 𝕟(b)) ← (𝕟(ℕ.𝐒(a)) → 𝕟(ℕ.𝐒(b)))
popShiftMap f(x) = shiftRepeat'(f(𝟎)) (f(𝐒(x)))
