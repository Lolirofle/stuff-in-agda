module Numeral.Finite.Relation.Order where

import      Lvl
open import Data
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Type

private variable an bn cn n : ℕ
private variable a : 𝕟(an)
private variable b : 𝕟(bn)
private variable c : 𝕟(cn)

_≤_ : 𝕟(an) → 𝕟(bn) → Type
_≤_ = IsTrue ∘₂ (_≤?_)

_≥_ : 𝕟(an) → 𝕟(bn) → Type
_≥_ = IsTrue ∘₂ (_≥?_)

_<_ : 𝕟(an) → 𝕟(bn) → Type
_<_ = IsTrue ∘₂ (_<?_)

_>_ : 𝕟(an) → 𝕟(bn) → Type
_>_ = IsTrue ∘₂ (_>?_)

_≡_ : 𝕟(an) → 𝕟(bn) → Type
_≡_ = IsTrue ∘₂ (_≡?_)

_≢_ : 𝕟(an) → 𝕟(bn) → Type
_≢_ = IsTrue ∘₂ (_≢?_)

-- TODO: open import Structure.Relator.Properties

import Numeral.Natural.Relation.Order as ℕ

[≤]-minimum : (𝟎{n} ≤ a)
[≤]-minimum {a = 𝟎}   = <>
[≤]-minimum {a = 𝐒 _} = <>

-- [≤]-maximum : (bound a ℕ.≤ n) → (a ≤ maximum{n})
-- [≤]-maximum {_}    {𝟎}            ℕ.[≤]-with-[𝐒]                 = <>
-- [≤]-maximum {𝐒 an} {𝐒 a} {.(𝐒 n)} (ℕ.[≤]-with-[𝐒] {y = n} ⦃ p ⦄) = [≤]-maximum {an}{a}{n} p
[≤]-maximum : (bound a ℕ.≤ 𝐒(n)) → (a ≤ maximum{n})
[≤]-maximum {a = 𝟎}         {𝟎}   (ℕ.succ _) = <>
[≤]-maximum {a = 𝟎}         {𝐒 _} (ℕ.succ _) = <>
[≤]-maximum {a = 𝐒 a}       {𝐒 x} (ℕ.succ p) = [≤]-maximum {a = a} p
[≤]-maximum {a = 𝐒 {𝟎} ()}  {𝟎}   (ℕ.succ _)
[≤]-maximum {a = 𝐒 {𝐒 n} a} {𝟎}   (ℕ.succ ())

[≤]-reflexivity-raw : (a ≤ a)
[≤]-reflexivity-raw {a = 𝟎}   = <>
[≤]-reflexivity-raw {a = 𝐒 a} = [≤]-reflexivity-raw {a = a}

[≤]-asymmetry-raw : (a ≤ b) → (b ≤ a) → (a ≡ b)
[≤]-asymmetry-raw {a = 𝟎} {b = 𝟎}     _ _ = <>
[≤]-asymmetry-raw {a = 𝐒 a} {b = 𝐒 b} p q = [≤]-asymmetry-raw {a = a}{b = b} p q

[≤]-transitivity-raw : (a ≤ b) → (b ≤ c) → (a ≤ c)
[≤]-transitivity-raw {a = 𝟎}   {b = 𝟎}   {c = 𝟎}   p q = <>
[≤]-transitivity-raw {a = 𝟎}   {b = 𝟎}   {c = 𝐒 c} p q = <>
[≤]-transitivity-raw {a = 𝟎}   {b = 𝐒 b} {c = 𝐒 c} p q = <>
[≤]-transitivity-raw {a = 𝐒 a} {b = 𝐒 b} {c = 𝐒 c} p q = [≤]-transitivity-raw {a = a} {b = b} {c = c} p q
