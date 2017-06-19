module Numeral.Natural.TotalOper{ℓ} where

import Level as Lvl
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Relation{ℓ}
open import Numeral.Natural.Relation.Properties{ℓ}
open import Relator.Equals{ℓ}{Lvl.𝟎}

-- Total predecessor function
𝐏 : (n : ℕ) → {{_ : n ≢ 𝟎}} → ℕ
𝐏(𝟎) {{[⊥]-proof}} with [⊥]-proof([≡]-intro)
...                   | ()
𝐏(𝐒(n)) = n

-- Total subtraction
_−_ : (a : ℕ) → (b : ℕ) → {{_ : a ≥ b}} → ℕ
_−_ a 𝟎 = a
_−_ 𝟎 (𝐒(b)) {{0≥𝐒b}} with ([<]-is-[≱] ([<][0]-minimum{b})) (0≥𝐒b)
...                      | ()
_−_ (𝐒(a)) (𝐒(b)) {{𝐒b≤𝐒a}} = _−_ a b {{[≤]-without-[𝐒] (𝐒b≤𝐒a)}}

-- Total division
_/_ : (a : ℕ) → (b : ℕ) → {{_ : b divides a}} → {{_ : b ≢ 0}} → ℕ
_/_ _ _ {{b-div-a}} {{_}} with divides-elim (b-div-a)
...                          | [∃]-intro (n) (b⋅n≡a) = n
