module Formalization.LambdaCalculus.SyntaxTransformation where

open import Formalization.LambdaCalculus
open import Functional.Instance
open import Numeral.Natural
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals

private variable d d₁ d₂ : ℕ
private variable x y : Term(d)

-- Increase the depth level of the given term by something.
-- Example: `depth-[≤](Var(2) : Term(5)) = Var(2) : Term(50)`
depth-[≤] : ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
depth-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
depth-[≤] (Abstract t)  = Abstract(depth-[≤] t)
depth-[≤] (Var x)       = Var(bound-[≤] infer x)

-- Increment the depth level of the given term by 1.
-- Example: `depth-𝐒(Var(2) : Term(5)) = Var(2) : Term(6)`
depth-𝐒 : Term(d) → Term(𝐒(d))
depth-𝐒 = depth-[≤]
-- depth-𝐒 (Apply(f)(x))       = Apply (depth-𝐒(f)) (depth-𝐒(x))
-- depth-𝐒 (Abstract(body))    = Abstract(depth-𝐒(body))
-- depth-𝐒 (Var(n))            = Var(bound-𝐒 (n))

Apply₊ : ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₂) → Term(d₁) → Term(d₂)
Apply₊ {d₁}{d₂} f(x) = Apply f(depth-[≤] {d₁}{d₂} (x))

{-
-- Increase all variables of the given term
var-[≤] : ∀{d₁ d₂} → ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
var-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
var-[≤] (Abstract t)  = Abstract(depth-[≤] t)
var-[≤] (Var x) = Var({!x + (d₂ − d₁)!}) where
  open import Numeral.Natural.TotalOper
-}

-- Increment all variables of the given term.
-- Example: `var-𝐒(Var(2) : Term(5)) = Var(3) : Term(6)`
-- Examples:
--   term : Term(1)
--   term = (1 ↦ (2 ↦ 2 ← 2) ← 0 ← 1 ← 0)
--
--   Then:
--   term               = 1 ↦ (2 ↦ 2 ← 2) ← 0 ← 1 ← 0
--   var-𝐒(term)        = 2 ↦ (3 ↦ 3 ← 3) ← 1 ← 2 ← 1
--   var-𝐒(var-𝐒(term)) = 3 ↦ (4 ↦ 4 ← 4) ← 2 ← 3 ← 2
var-𝐒 : Term(d) → Term(𝐒(d))
var-𝐒 (Apply(f)(x))       = Apply (var-𝐒(f)) (var-𝐒(x))
var-𝐒 (Abstract{d}(body)) = Abstract{𝐒(d)} (var-𝐒(body))
var-𝐒 (Var{𝐒(d)}(n))      = Var{𝐒(𝐒(d))} (𝐒(n))

-- Substitutes the most recent free variable with a term in a term, while also decrementing them.
-- `substitute val term` is the term where all occurences in `term` of the outer-most variable is replaced with the term `val`.
-- Examples:
--   substituteOuterVar x (Var(0) : Term(1)) = x
--   substituteOuterVar x ((Apply (Var(1)) (Var(0))) : Term(2)) = Apply (Var(0)) x
--   substituteOuterVar (𝜆 0 0) ((𝜆 1 1) ← 0) = ((𝜆 0 0) ← (𝜆 0 0))
--   substituteOuterVar (𝜆 0 0) ((𝜆 1 1 ← 0) ← 0) = (((𝜆 0 0) ← (𝜆 0 0)) ← (𝜆 0 0))
substituteVar0 : Term(d) → Term(𝐒(d)) → Term(d)
substituteVar0 val (Apply(f)(x))    = Apply (substituteVar0 val f) (substituteVar0 val x)
substituteVar0 val (Abstract(body)) = Abstract (substituteVar0 (var-𝐒 val) body)
substituteVar0 val (Var(𝟎))         = val
substituteVar0 val (Var(𝐒(v)))      = Var v

{-
substituteMap : (𝕟(d₁) → Term(d₂)) → Term(d₁) → Term(d₂)
substituteMap F (Apply(f)(x))    = Apply (substituteMap F (f)) (substituteMap F (x))
substituteMap F (Var(v))         = F(v)
substituteMap F (Abstract(body)) = Abstract (substituteMap F (body)) -- TODO: Probably incorrect
-}

-- Substituting the outer variable of `var-𝐒 x` yields `x`.
-- This is useful because `substituteVar0` uses `var-𝐒` in its definition.
substituteVar0-var-𝐒 : (substituteVar0 y (var-𝐒 x) ≡ x)
substituteVar0-var-𝐒 {d}{y}{Apply f x}  rewrite substituteVar0-var-𝐒 {d}{y}{f} rewrite substituteVar0-var-𝐒 {d}{y}{x} = [≡]-intro
substituteVar0-var-𝐒 {d}{y}{Abstract x} rewrite substituteVar0-var-𝐒 {𝐒 d}{var-𝐒 y}{x} = [≡]-intro
substituteVar0-var-𝐒 {_}{_}{Var 𝟎}      = [≡]-intro
substituteVar0-var-𝐒 {_}{_}{Var(𝐒 _)}   = [≡]-intro
{-# REWRITE substituteVar0-var-𝐒 #-}
