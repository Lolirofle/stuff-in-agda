module Lvl where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to 𝟎; lsuc to 𝐒)

import Numeral.Natural as ℕ

instance
  Level-From-ℕ : ℕ.From-ℕ (Level)
  ℕ.from-ℕ ⦃ Level-From-ℕ ⦄ (ℕ.𝟎)    = 𝟎
  ℕ.from-ℕ ⦃ Level-From-ℕ ⦄ (ℕ.𝐒(n)) = 𝐒(ℕ.from-ℕ(n))
