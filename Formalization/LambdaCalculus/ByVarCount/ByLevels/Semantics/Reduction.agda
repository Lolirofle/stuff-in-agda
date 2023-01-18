-- Definitions of reduction steps for normalization of terms.
-- "Small-step" semantics.
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Functions
open import Graph.Walk using (at ; prepend) renaming (Walk to ReflexiveTransitiveClosure)
open import Numeral.Natural
open import Numeral.Finite
open import Relator.ReflexiveTransitiveClosure using (SymmetricClosure ; TransitiveClosure)
import      Structure.Function.Names as Names
import      Structure.Relator.Names as Names
open import Syntax.Number
open import Type

private variable d d₁ d₂ : ℕ
private variable f g x y : Term(d)

module _ {ℓ} (_⇴_ : ∀{d} → Term(d) → Term(d) → Type{ℓ}) where
  -- β-rule (beta reduction/expansion).
  -- The beta reduction rule states: a term of the form `f(x)` reduces to `f[0 ≔ x]`.
  β-rule : Type
  β-rule = ∀{d}{f}{x : Term(d)} → (Apply(Abstract(f))(x) ⇴ substituteVar maximum x f)

  -- η-rule (eta reduction/expansion).
  -- The eta reduction rule states: a term of the form `λx. f(x)` reduces to `f`.
  η-rule : Type
  η-rule = ∀{d}{f : Term(𝐒(d))} → (Abstract(Apply(varShift𝐒 maximum f)(Var(maximum))) ⇴ f)

data _β⇴_ : Term(d) → Term(d) → Type{0} where
  β             : β-rule(_β⇴_)
  cong-applyₗ   : Names.Compatible₁(_β⇴_)(_β⇴_)(\f → Apply f x)
  cong-applyᵣ   : Names.Compatible₁(_β⇴_)(_β⇴_)(\x → Apply f x)

_β⇴*_ : Term(d) → Term(d) → Type
_β⇴*_ = ReflexiveTransitiveClosure(_β⇴_)

_β⥈_ : Term(d) → Term(d) → Type
_β⥈_ = SymmetricClosure(_β⇴_)

_β⥈*_ : Term(d) → Term(d) → Type
_β⥈*_ = ReflexiveTransitiveClosure(_β⥈_)

-- Reduction of expressions.
-- `a ⇴ b` states that `a` reduces to `b` in one step using β-reduction, η-reduction or compatibility rules.
-- Note: cong-applyₗ, cong-applyᵣ and the reductions can be applied in any order. Many evaluation strategies have a fixed order. (TODO: Restrict evaluation strategies by checking the proof terms? See below for the start on isStrict)
-- TODO: cong-abstract is sometimes not included, for example in the call by value evaluation strategy? Is it required for the encoding of ℕ?
data _⇴_ : Term(d) → Term(d) → Type{0} where
  β             : β-rule(_⇴_)
  η             : η-rule(_⇴_)
  cong-applyₗ   : Names.Compatible₁(_⇴_)(_⇴_)(\f → Apply f x)
  cong-applyᵣ   : Names.Compatible₁(_⇴_)(_⇴_)(\x → Apply f x)
  cong-abstract : Names.Compatible₁(_⇴_)(_⇴_)(Abstract{d})

_⇴*_ : Term(d) → Term(d) → Type
_⇴*_ = ReflexiveTransitiveClosure(_⇴_)

_⥈_ : Term(d) → Term(d) → Type
_⥈_ = SymmetricClosure(_⇴_)

_⥈*_ : Term(d) → Term(d) → Type
_⥈*_ = TransitiveClosure(_⥈_)

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming

isCallByNameβ : (x β⇴ y) → Bool
isCallByNameβ β               = 𝑇
isCallByNameβ (cong-applyₗ p) = isCallByNameβ p
isCallByNameβ (cong-applyᵣ _) = 𝐹

isCallByNameβ* : (x β⇴* y) → Bool
isCallByNameβ* at             = 𝑇
isCallByNameβ* (prepend p pl) = isCallByNameβ p && isCallByNameβ* pl

{-
isStrict : (x ⇴* y) → Bool
isStrict (super (β {f = f}{x = x})) = {!isNormal x!}
isStrict (super η) = 𝑇
isStrict (super(cong-applyₗ p)) = isStrict(super p) -- TODO: Should this be possible?
isStrict (super(cong-applyᵣ p)) = isStrict(super p)
isStrict (super(cong-abstract p)) = isStrict(super p)
isStrict refl = 𝑇
isStrict (trans p q) = isStrict p && isStrict q
-}
