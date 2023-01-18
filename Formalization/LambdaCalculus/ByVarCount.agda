module Formalization.LambdaCalculus.ByVarCount where

import      Lvl
open import Data
open import Numeral.Natural
open import Numeral.Finite
open import Syntax.Number
open import Type

-- A lambda term (A term in the language of lambda calculus).
-- This is encoded using an "abstraction depth" which ensures that every term is well-formed (no undefined variable names).
-- `Term(𝟎)` is the type of closed terms, terms that have no unbound variables.
--   In this representation, it means that there are no occurrences of `Var(_)` in a term.
-- `Term(𝐒(n))` for some `n` is the types of open terms with possibly `n` number of different variables, terms that have unbound variables.
--   In this representation, it means that there can be `Var(i)` for `i < n` in a term.
-- This type of encoding is also called: DeBrujin syntax.
data Term : ℕ → Type{0} where
  -- The term that represent applying the second term to the first term.
  -- Representation in function notation:
  --   (Apply f(x)) is f(x)
  Apply : ∀{d} → Term(d) → Term(d) → Term(d)

  -- The term that represent a binding to a new variable (variable introduction).
  -- Representation in function notation:
  --   (Abstract{n} term) is (xₙ ↦ term)
  Abstract : ∀{d} → Term(𝐒(d)) → Term(d)

  -- The term that represent a specific variable in scope.
  -- Representation in function notation:
  --   (Var(n)) is xₙ
  Var : ∀{d} → 𝕟(d) → Term(d)

-- An expression in the language of lambda calculus is a closed term.
Expression : Type{0}
Expression = Term(0)

module _
  {ℓ} (P : ∀{d} → Term(d) → Type{ℓ})
  (papp : ∀{d}{f x} → P(f) → P(x) → P(Apply{d} f x))
  (pabs : ∀{d}{body} → P(body) → P(Abstract{d} body))
  (pvar : ∀{d}(v) → P(Var{d} v))
  where

  elim : ∀{d} → (t : Term(d)) → P(t)
  elim(Apply f x)        = papp(elim f) (elim x)
  elim(Abstract{d} body) = pabs(elim body)
  elim(Var{𝐒(d)} v)      = pvar v
