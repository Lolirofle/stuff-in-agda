-- TODO: Maybe not like this
module Numeral.Finite.Relation.Order2 where

import      Lvl
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
open import Type

private variable an bn cn n : ℕ
private variable a : 𝕟(an)
private variable b : 𝕟(bn)
private variable c : 𝕟(cn)

Positive : 𝕟(n)  → Type
Positive = IsTrue ∘ positive?

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Numeral.Finite
open import Numeral.Sign

-- Compare
module _ {ℓ}{T : Type{ℓ}} (z : T) (lt : T) (gt : T) (st : T → T) where
  data Compare : T → ∀{a b} → 𝕟(a) → 𝕟(b) → Type{ℓ} where
    zero  : Compare z  (𝟎{an})   (𝟎{bn})
    left  : Compare lt (𝟎{an})   (𝐒{bn} b)
    right : Compare gt (𝐒{an} a) (𝟎{bn})
    step  : ∀{s} → Compare s a b → Compare (st s) (𝐒(a)) (𝐒(b))

-- .⦃ pos-A : ℕ.Positive(an) ⦄ → .⦃ pos-A : ℕ.Positive(an) ⦄ → Compare z  (minimum{an})   (minimum{bn})

-- Equality check
_≡_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_≡_ = Compare 𝐹 𝑇 𝐹 id 𝑇

-- Non-equality check
_≢_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_≢_ = Compare 𝑇 𝐹 𝑇 id 𝑇

-- Lesser-than check
_<_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_<_ = Compare 𝑇 𝐹 𝐹 id 𝑇

-- Lesser-than or equals check
_≤_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_≤_ = Compare 𝑇 𝑇 𝐹 id 𝑇

-- Greater-than check
_>_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_>_ = Compare 𝐹 𝐹 𝑇 id 𝑇

-- Greater-than or equals check
_≥_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Type
_≥_ = Compare 𝐹 𝑇 𝑇 id 𝑇
