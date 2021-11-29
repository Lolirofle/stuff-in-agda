module Formalization.LambdaCalculus where

import      Lvl
open import Data
open import Numeral.Natural
open import Numeral.Finite
open import Syntax.Number
open import Type

-- A lambda term (A term in the language of lambda calculus).
-- This is encoded with an abstraction depth which ensures that every term is well-formed.
-- `Term(𝟎)` is the type of closed terms, terms that have no unbound variables.
--   In this representation, it means that there are no occurrences of `Var(_)` in a term.
-- `Term(𝐒(n))` for some `n` is the types of open terms with possibly `n` number of different variables, terms that have unbound variables.
--   In this representation, it means that there can be `Var(i)` for `i < n` in a term.
data Term : ℕ → Type{0} where
  -- The term which represents applying the second term on the first term.
  -- Representation in function notation:
  --   (Apply f(x)) is f(x)
  Apply : ∀{d} → Term(d) → Term(d) → Term(d)

  -- The term which represents bounding a new variable (introducing a variable).
  -- Representation in function notation:
  --   (Abstract{n} term) is (xₙ ↦ term)
  Abstract : ∀{d} → Term(𝐒(d)) → Term(d)

  -- The term which represents a specific variable in scope.
  -- Representation in function notation:
  --   (Var(n)) is xₙ
  Var : ∀{d} → 𝕟(d) → Term(d)

-- An expression in the language of lambda calculus is a closed term.
Expression : Type{0}
Expression = Term(0)

module VarNumeralSyntax where
  -- Syntax for writing Var as a numeral.
  instance
    Term-from-ℕ : ∀{N} → Numeral(Term(N)) (Numeral.Restriction(𝕟-from-ℕ {N}))
    num ⦃ Term-from-ℕ ⦄ (n) = Var(num n)

module OperSyntax where
  open VarNumeralSyntax public

  infixr 100 _↦_
  infixl 101 _←_

  pattern _↦_ d expr = Term.Abstract{d} expr
  pattern _←_ a b    = Term.Apply a b

module ExplicitLambdaSyntax where
  open VarNumeralSyntax public

  infixl 101 _←_

  pattern 𝜆 d expr = Term.Abstract{d} expr
  pattern _←_ a b  = Term.Apply a b
