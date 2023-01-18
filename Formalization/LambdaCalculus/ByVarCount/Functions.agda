module Formalization.LambdaCalculus.ByVarCount.Functions where

open import Data
import      Data.Option.Functions as Option
open import Formalization.LambdaCalculus.ByVarCount
open import Functional
open import Functional.Instance
open import Numeral.Natural
open import Numeral.Finite as 𝕟 using (𝕟 ; 𝟎 ; 𝐒)
import      Numeral.Finite.Bound as 𝕟
import      Numeral.Finite.Oper as 𝕟
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs

private variable d d₁ d₂ : ℕ
private variable n : 𝕟(d)
private variable x y : Term(d)

module _
  (F : ℕ → ℕ)
  (var : ∀{d} → 𝕟(d) → 𝕟(F(d)))
  (abstr : ∀{d} → Term(F(𝐒(d))) → Term(𝐒(F(d))))
  where

  varMap : Term(d) → Term(F(d))
  varMap = elim(\{d} _ → Term(F(d))) Apply (Abstract ∘ abstr) (Var ∘ var)

-- Increase the depth level of the given term by something.
-- Example: `depth-[≤](Var(2) : Term(5)) = Var(2) : Term(50)`
depth-[≤] : ⦃ ord : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
depth-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
depth-[≤] (Abstract t)  = Abstract(depth-[≤] t)
depth-[≤] (Var x)       = Var(𝕟.bound-[≤] infer x)

-- Increment the depth level of the given term by 1.
-- Example: `depth-𝐒(Var(2) : Term(5)) = Var(2) : Term(6)`
-- Alternative implementation:
--   depth-𝐒 (Apply(f)(x))    = Apply (depth-𝐒(f)) (depth-𝐒(x))
--   depth-𝐒 (Abstract(body)) = Abstract(depth-𝐒(body))
--   depth-𝐒 (Var(n))         = Var(bound-𝐒 (n))
depth-𝐒 : Term(d) → Term(𝐒(d))
depth-𝐒 = depth-[≤]

{-
-- Increase all variables of the given term
var-[≤] : ∀{d₁ d₂} → ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
var-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
var-[≤] (Abstract t)  = Abstract(depth-[≤] t)
var-[≤] (Var x) = Var({!x + (d₂ − d₁)!}) where
  open import Numeral.Natural.TotalOper
-}

varShift𝐒 : 𝕟(𝐒(d)) → Term(d) → Term(𝐒(d))
varShift𝐒 n (Apply f x)        = Apply (varShift𝐒 n f) (varShift𝐒 n x)
varShift𝐒 n (Abstract{d} body) = Abstract{𝐒(d)} (varShift𝐒(𝕟.bound-𝐒(n)) body)
varShift𝐒 n (Var{𝐒(d)} v)      = Var{𝐒(𝐒(d))} (𝕟.shift𝐒 n v)

varShift𝐒ᵢ = \{d}{n} → varShift𝐒{d} n
varShift𝐒₀ = \{d} → varShift𝐒(𝟎 {d})
varShift𝐒₁ = \{d} → varShift𝐒(𝐒(𝟎 {d}))
varShift𝐒₂ = \{d} → varShift𝐒(𝐒(𝐒(𝟎 {d})))
varShift𝐒₃ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝟎 {d}))))
varShift𝐒₄ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d})))))
varShift𝐒₅ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d}))))))
varShift𝐒₆ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d})))))))
varShift𝐒₇ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d}))))))))
varShift𝐒₈ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d})))))))))
varShift𝐒₉ = \{d} → varShift𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎 {d}))))))))))
varShift𝐒Outermost = \{d} → varShift𝐒{d} 𝕟.maximum

{-
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
-- `substituteVar0 val term` is the term where all occurences in `term` of the outer-most variable is replaced with the term `val`.
-- Examples:
--   substituteVar0 x (Var(0) : Term(1)) = x
--   substituteVar0 x ((Apply (Var(1)) (Var(0))) : Term(2)) = Apply (Var(0)) x
--   substituteVar0 (𝜆 0 0) ((𝜆 1 1) ← 0) = ((𝜆 0 0) ← (𝜆 0 0))
--   substituteVar0 (𝜆 0 0) ((𝜆 1 1 ← 0) ← 0) = (((𝜆 0 0) ← (𝜆 0 0)) ← (𝜆 0 0))
substituteVar0 : Term(d) → Term(𝐒(d)) → Term(d)
substituteVar0 val (Apply(f)(x))    = Apply (substituteVar0 val f) (substituteVar0 val x)
substituteVar0 val (Abstract(body)) = Abstract (substituteVar0 (var-𝐒 val) body)
substituteVar0 val (Var v)          = Option.partialMap val Var (𝕟.Optional.𝐏(v))
-}

substituteVar : 𝕟(𝐒(d)) → Term(d) → Term(𝐒(d)) → Term(d)
substituteVar n val (Apply(f)(x))    = Apply (substituteVar n val f) (substituteVar n val x)
substituteVar n val (Abstract(body)) = Abstract (substituteVar (𝕟.bound-𝐒(n)) (varShift𝐒 n val) body)
substituteVar n val (Var v)          = Option.partialMap val Var (𝕟.Optional.shift𝐏 n v)
substituteVarOutermost = \{d} → substituteVar{d} 𝕟.maximum

{-
open import Type

open import Numeral.Natural.Oper
substituteMap : (∀{d} → 𝕟(d₁ + d) → Term(d₂ + d)) → Term(d₁) → Term(d₂)
substituteMap F (Apply(f)(x))    = Apply (substituteMap F f) (substituteMap F x)
substituteMap F (Abstract(body)) = Abstract (substituteMap F body)
substituteMap F (Var(v))         = F(v)
-}

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
-- open import Data.Boolean.Stmt.Logic
open import Logic.Propositional
-- import      Numeral.Finite.Oper.Comparisons as 𝕟
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Type

module _ (b : ∀{d} → 𝕟(d) → Bool) where
  isVars : Term(d) → Bool
  isVars(Apply f x)     = isVars f && isVars x
  isVars(Abstract body) = isVars body
  isVars(Var v)         = b(v)

module _ {ℓ} (b : ∀{d} → 𝕟(d) → Type{ℓ}) where
  IsVars : Term(d) → Type
  IsVars(Apply f x)     = IsVars f ∧ IsVars x
  IsVars(Abstract body) = IsVars body
  IsVars(Var v)         = b(v)

module _ (s : ℕ → ℕ) where
  isVarFree : ℕ → Term(d) → Bool
  isVarFree n (Apply f x)     = isVarFree n f && isVarFree n x
  isVarFree n (Abstract body) = isVarFree (s(n)) body
  isVarFree n (Var v)         = n ℕ.≢? 𝕟.toℕ(v)

isVarLevelFree : ℕ → Term(d) → Bool
isVarLevelFree = isVarFree id
IsVarLevelFree = \{d} → IsTrue ∘₂ isVarLevelFree{d}

isVarIndexFree : ℕ → Term(d₂) → Bool
isVarIndexFree = isVarFree 𝐒
IsVarIndexFree = \{d} → IsTrue ∘₂ isVarIndexFree{d}



open import Numeral.Finite.Oper.Proofs as Option
open import Relator.Equals

substituteVar-varShift𝐒 : (substituteVar n y (varShift𝐒 n x) ≡ x)
substituteVar-varShift𝐒 {d} {n} {y} {Apply f x}
  rewrite substituteVar-varShift𝐒 {d}{n}{y}{f}
  rewrite substituteVar-varShift𝐒 {d}{n}{y}{x}
  = [≡]-intro
substituteVar-varShift𝐒 {d} {n} {y} {Abstract x}
  rewrite substituteVar-varShift𝐒 {𝐒(d)}{𝕟.bound-𝐒(n)}{varShift𝐒 n y}{x}
  = [≡]-intro
substituteVar-varShift𝐒 {𝐒 d} {n} {y} {Var v}
  rewrite shift𝐏-shift𝐒-inverse₌ {c = n}{x = v}
  = [≡]-intro
{-# REWRITE substituteVar-varShift𝐒 #-}
