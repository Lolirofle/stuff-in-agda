module Formalization.LambdaCalculus.ByVarCount.ByIndices.Semantics.Reduction where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Numeral.Natural
open import Numeral.Finite
open import Relator.ReflexiveTransitiveClosure
import      Structure.Function.Names as Names
import      Structure.Relator.Names as Names
open import Syntax.Number
open import Type

private variable d d₁ d₂ : ℕ
private variable f g x y : Term(d)

module _ {ℓ} (_⇴_ : ∀{d} → Term(d) → Term(d) → Type{ℓ}) where
  -- β-reduction (beta) with its compatible closure over `Apply`.
  -- The beta reduction rule that states: a term of form `f(x)` reduces to `f[0 ≔ x]`.
  β-reduction : Type
  β-reduction = ∀{d}{f}{x : Term(d)} → (Apply(Abstract(f))(x) ⇴ substituteVar maximum (x)(f)) -- TODO: maximum?

  -- η-reduction (eta).
  -- The eta reduction rule that states: a term of form `x ↦ f(x)` reduces to `f`.
  η-reduction : Type
  η-reduction = ∀{d}{f : Term(𝐒(d))} → (Abstract(Apply(varShift𝐒 maximum (f)) (Var(𝟎))) ⇴ f) -- TODO: maximum?

data _β⇴_ : Term(d) → Term(d) → Type{0} where
  β             : β-reduction(_β⇴_)
  cong-applyₗ   : Names.Compatible₁(_β⇴_)(_β⇴_)(\f → Apply f x)
  cong-applyᵣ   : Names.Compatible₁(_β⇴_)(_β⇴_)(\x → Apply f x)

_β⇴*_ : Term(d) → Term(d) → Type
_β⇴*_ = ReflexiveTransitiveClosure(_β⇴_)

_β⥈_ : Term(d) → Term(d) → Type
_β⥈_ = SymmetricClosure(_β⇴_)

_β⥈*_ : Term(d) → Term(d) → Type
_β⥈*_ = ReflexiveTransitiveClosure(_β⥈_)

-- Reduction of expressions
-- Note: cong-applyₗ, cong-applyᵣ and the reductions can be applied in any order. Many evaluation strategies have a fixed order.
-- TODO: cong-abstract is usually not included, specifically for the call by value evaluation strategy? Is it required for the encoding of ℕ?
data _⇴_ : Term(d) → Term(d) → Type{0} where
  β             : β-reduction(_⇴_)
  η             : η-reduction(_⇴_)
  cong-applyₗ   : Names.Compatible₁(_⇴_)(_⇴_)(\f → Apply f x)
  cong-applyᵣ   : Names.Compatible₁(_⇴_)(_⇴_)(\x → Apply f x)
  cong-abstract : Names.Compatible₁(_⇴_)(_⇴_)(Abstract{d})

_⇴*_ : Term(d) → Term(d) → Type
_⇴*_ = ReflexiveTransitiveClosure(_⇴_)

_⥈_ : Term(d) → Term(d) → Type
_⥈_ = SymmetricClosure(_⇴_)

_⥈*_ : Term(d) → Term(d) → Type
_⥈*_ = ReflexiveTransitiveClosure(_⥈_)
