module Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs where

import      Lvl
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
open import Graph.Walk
open import Numeral.Natural
open import Relator.ReflexiveTransitiveClosure
import      Structure.Function.Names as Names
open import Structure.Function

private variable d d₁ d₂ : ℕ
private variable f g x y : Term(d)

open import Graph.Walk.Proofs using (Walk-super ; Walk-sub ; Walk-transitivity ; Walk-reflexivity ; Walk-subtransitivityₗ) public

[⇴*]-super-function : ∀{F : Term(d₁) → Term(d₂)} → ⦃ Compatible₁(_⇴_)(_⇴_)(F) ⦄ → Compatible₁(_⇴*_)(_⇴*_)(F)
[⇴*]-super-function {F = F} = intro proof where
  proof : Names.Compatible₁(_⇴*_)(_⇴*_)(F)
  proof at = at
  proof (prepend p q) = prepend (compatible₁(_⇴_)(_⇴_)(F) p) (proof q)

instance
  [⇴]-Applyₗ-function : Compatible₁(_⇴_)(_⇴_)(\f → Apply f x)
  [⇴]-Applyₗ-function = intro cong-applyₗ

instance
  [⇴]-Applyᵣ-function : Compatible₁(_⇴_)(_⇴_)(\x → Apply f x)
  [⇴]-Applyᵣ-function = intro cong-applyᵣ

instance
  [⇴]-Abstract-function : Compatible₁(_⇴_)(_⇴_)(Abstract{d})
  [⇴]-Abstract-function = intro cong-abstract

instance
  [⇴*]-Applyₗ-function : Compatible₁(_⇴*_)(_⇴*_)(\f → Apply f x)
  [⇴*]-Applyₗ-function = [⇴*]-super-function

instance
  [⇴*]-Applyᵣ-function : Compatible₁(_⇴*_)(_⇴*_)(\x → Apply f x)
  [⇴*]-Applyᵣ-function = [⇴*]-super-function

instance
  [⇴*]-Abstract-function : Compatible₁(_⇴*_)(_⇴*_)(Abstract{d})
  [⇴*]-Abstract-function = [⇴*]-super-function

{-
[⇴]-lift : ⦃ IsOutermostLevelFree x ⦄ → (x ⇴ y) → ((x ↑) ⇴ (y ↑))
[⇴]-lift (β {f = f}{x = x}) rewrite var-𝐒-substituteVar0 {x = f}{y = x} ⦃ {!!} ⦄ = β
[⇴]-lift η = η
[⇴]-lift (cong-applyₗ xy) = cong-applyₗ ([⇴]-lift ⦃ {!!} ⦄ xy)
[⇴]-lift (cong-applyᵣ xy) = cong-applyᵣ ([⇴]-lift ⦃ {!!} ⦄ xy)
[⇴]-lift (cong-abstract xy) = cong-abstract ([⇴]-lift xy)
-}

[β⇴*]-super-function : ∀{F : Term(d₁) → Term(d₂)} → ⦃ Compatible₁(_β⇴_)(_β⇴_)(F) ⦄ → Compatible₁(_β⇴*_)(_β⇴*_)(F)
[β⇴*]-super-function {F = F} = intro proof where
  proof : Names.Compatible₁(_β⇴*_)(_β⇴*_)(F)
  proof at = at
  proof (prepend p q) = prepend (compatible₁(_β⇴_)(_β⇴_)(F) p) (proof q)

instance
  [β⇴]-Applyₗ-function : Compatible₁(_β⇴_)(_β⇴_)(\f → Apply f x)
  [β⇴]-Applyₗ-function = intro cong-applyₗ

instance
  [β⇴]-Applyᵣ-function : Compatible₁(_β⇴_)(_β⇴_)(\x → Apply f x)
  [β⇴]-Applyᵣ-function = intro cong-applyᵣ

instance
  [β⇴*]-Applyₗ-function : Compatible₁(_β⇴*_)(_β⇴*_)(\f → Apply f x)
  [β⇴*]-Applyₗ-function = [β⇴*]-super-function

instance
  [β⇴*]-Applyᵣ-function : Compatible₁(_β⇴*_)(_β⇴*_)(\x → Apply f x)
  [β⇴*]-Applyᵣ-function = [β⇴*]-super-function
