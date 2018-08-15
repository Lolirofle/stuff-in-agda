module Numeral.Natural.Oper.Comparisons.Proofs{ℓ} where

open import Data.Boolean.AsSet
open import Data.Boolean
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals{ℓ}

instance
  [≤?]-𝟎 : ∀{n} → BoolIsTrue{ℓ}(𝟎 ≤? n)
  [≤?]-𝟎 = [⊤]-intro

instance
  [≤?]-𝐒 : ∀{n} → BoolIsTrue{ℓ}(n ≤? n)
  [≤?]-𝐒 {𝟎}    = [⊤]-intro
  [≤?]-𝐒 {𝐒(n)} = [≤?]-𝐒 {n}

[<?]-positive : ∀{n} → (𝟎 <? n) ≡ positive?(n)
[<?]-positive {𝟎}    = [≡]-intro
[<?]-positive {𝐒(_)} = [≡]-intro
{-# REWRITE [<?]-positive #-}

[≤?]-positive : ∀{n} → (𝐒(𝟎) ≤? n) ≡ positive?(n)
[≤?]-positive {𝟎}    = [≡]-intro
[≤?]-positive {𝐒(_)} = [≡]-intro
{-# REWRITE [≤?]-positive #-}

[≢?]-positive : ∀{n} → (n ≢? 𝟎) ≡ positive?(n)
[≢?]-positive {𝟎}    = [≡]-intro
[≢?]-positive {𝐒(_)} = [≡]-intro
