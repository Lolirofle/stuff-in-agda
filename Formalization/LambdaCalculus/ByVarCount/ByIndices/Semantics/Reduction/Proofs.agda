module Formalization.LambdaCalculus.ByVarCount.ByIndices.Semantics.Reduction.Proofs where

import      Lvl
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByIndices.Semantics.Reduction
open import Numeral.Natural
open import Relator.ReflexiveTransitiveClosure
import      Structure.Function.Names as Names
open import Structure.Function

private variable d : ℕ
private variable f g x y : Term(d)

instance
  [⇴*]-Applyₗ-function : Compatible₁(_⇴*_)(_⇴*_)(\f → Apply f x)
  [⇴*]-Applyₗ-function = intro proof where
    proof : Names.Compatible₁(_⇴*_)(_⇴*_)(\f → Apply f x)
    proof (super p)   = super (cong-applyₗ p)
    proof refl        = refl
    proof (trans p q) = trans (proof p) (proof q)

instance
  [⇴*]-Applyᵣ-function : Compatible₁(_⇴*_)(_⇴*_)(\x → Apply f x)
  [⇴*]-Applyᵣ-function = intro proof where
    proof : Names.Compatible₁(_⇴*_)(_⇴*_)(\x → Apply f x)
    proof (super p)   = super (cong-applyᵣ p)
    proof refl        = refl
    proof (trans p q) = trans (proof p) (proof q)

instance
  [⇴*]-Abstract-function : Compatible₁(_⇴*_)(_⇴*_)(Abstract{d})
  [⇴*]-Abstract-function = intro proof where
    proof : Names.Compatible₁(_⇴*_)(_⇴*_)(Abstract{d})
    proof (super p)   = super (cong-abstract p)
    proof refl        = refl
    proof (trans p q) = trans (proof p) (proof q)
