module Miscellaneous.FiniteByPair where

import      Lvl
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.Proofs.Rewrite
open import Type

data 𝕟₌ : ℕ → Type{Lvl.𝟎} where
  fin : (n : ℕ) → (rest : ℕ) → 𝕟₌(n ℕ.+ rest)

private variable A B C N : ℕ
private variable a b c n : 𝕟₌(N)

𝟎 : 𝕟₌(N)
𝟎 {N} = fin ℕ.𝟎 N

𝐒 : 𝕟₌(N) → 𝕟₌(ℕ.𝐒(N))
𝐒(fin n rest) = fin (ℕ.𝐒(n)) rest

module _
  {ℓ}
  (T : ∀{N} → 𝕟₌(N) → Type{ℓ})
  (base : ∀{N} → T{N}(𝟎))
  (step : ∀{N} → (i : 𝕟₌(N)) → T(i) → T(𝐒(i)))
  where

  𝕟₌-elim : ∀{N} → (n : 𝕟₌(N)) → T(n)
  𝕟₌-elim(fin ℕ.𝟎     rest) = base
  𝕟₌-elim(fin (ℕ.𝐒 n) rest) = step _ (𝕟₌-elim(fin n rest))
