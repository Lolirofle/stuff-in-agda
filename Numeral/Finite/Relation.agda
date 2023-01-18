module Numeral.Finite.Relation where

open import Data.Boolean.Stmt
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Logic.Propositional
open import Logic
open import Relator.Equals

private variable N : ℕ
private variable n a b : 𝕟(N)

Positive : 𝕟(N) → Stmt
Positive(n) = IsTrue(positive? n)

zero-not-positive : ¬ Positive(𝟎 {N})
zero-not-positive ()

positive-not-zero : ⦃ _ : Positive(n) ⦄ → (n ≢ 𝟎)
positive-not-zero {_} {𝟎}   ⦃ () ⦄
positive-not-zero {_} {𝐒 _} ⦃ _ ⦄ ()

non-zero-positive : (n ≢ 𝟎) → Positive(n)
non-zero-positive {_}{𝟎}   p = p [≡]-intro
non-zero-positive {_}{𝐒 n} p = [⊤]-intro

[<]-to-positive : IsTrue(a <? b) → Positive(b)
[<]-to-positive {a = 𝟎}  {b = 𝐒 _} _ = [⊤]-intro
[<]-to-positive {a = 𝐒 _}{b = 𝐒 _} _ = [⊤]-intro

[>]-to-positive : IsTrue(a >? b) → Positive(a)
[>]-to-positive {a = 𝐒 _}{b = 𝟎}   _ = [⊤]-intro
[>]-to-positive {a = 𝐒 _}{b = 𝐒 _} _ = [⊤]-intro

[≢]-to-positive : IsTrue(n ≢? 𝟎 {N}) → Positive(n)
[≢]-to-positive {n = 𝐒 _} _ = [⊤]-intro

[≤]-to-positive : IsTrue(a ≤? b) → Positive(a) → Positive(b)
[≤]-to-positive {a = 𝐒 _} {b = 𝐒 _} _ _ = [⊤]-intro

[≥]-to-positive : IsTrue(a ≥? b) → Positive(b) → Positive(a)
[≥]-to-positive {a = 𝐒 _} {b = 𝐒 _} _ _ = [⊤]-intro
