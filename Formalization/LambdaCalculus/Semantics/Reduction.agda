module Formalization.LambdaCalculus.Semantics.Reduction where

import      Lvl
open import Data
open import Formalization.LambdaCalculus
open import Formalization.LambdaCalculus.SyntaxTransformation
open import Numeral.Natural
open import Numeral.Finite
open import Relator.ReflexiveTransitiveClosure
open import Syntax.Number
open import Type

private variable d d₁ d₂ : ℕ
private variable f g x y : Term(d)

-- β-reduction (beta) with its compatible closure over `Apply`.
-- Reduces a term of form `f(x)` to `f[0 ≔ x]`.
data _β⇴_ : Term(d₁) → Term(d₂) → Type{1} where
  β : {f : Term(𝐒(d))}{x : Term(d)} → (Apply(Abstract(f))(x) β⇴ substituteVar0(x)(f))
  cong-applyₗ : (f β⇴ g) → (Apply f(x) β⇴ Apply g(x)) -- TODO: cong-applyₗ and cong-applyᵣ can be applied in any order, but many evaluation strategies have a fixed order. How should this be represented?
  cong-applyᵣ : (x β⇴ y) → (Apply f(x) β⇴ Apply f(y))
  cong-abstract : (x β⇴ y) → (Abstract x β⇴ Abstract y) -- TODO: Sometimes this is not included, specifically for the call by value evaluation strategy? But it seems to be required for the encoding of ℕ?

-- η-reduction (eta). (TODO: May require more introductions like β have)
-- Reduces a term of form `x ↦ f(x)` to `f`.
data _η⇴_ : Term(d₁) → Term(d₂) → Type{1} where
  η : (Abstract(Apply(f)(Var(maximum))) η⇴ f)

-- Reduction of expressions (TODO: May require more introductions like β have)
data _⇴_ : Term(d₁) → Term(d₂) → Type{1} where
  β : (Apply(Abstract(f))(x) ⇴ substituteVar0(x)(f))
  η : (Abstract(Apply(f)(Var(maximum))) ⇴ f)

_β⇴*_ : Term(d) → Term(d) → Type
_β⇴*_ = ReflexiveTransitiveClosure(_β⇴_)

_β⥈_ : Term(d) → Term(d) → Type
_β⥈_ = SymmetricClosure(_β⇴_)

_β⥈*_ : Term(d) → Term(d) → Type
_β⥈*_ = ReflexiveTransitiveClosure(_β⥈_)
