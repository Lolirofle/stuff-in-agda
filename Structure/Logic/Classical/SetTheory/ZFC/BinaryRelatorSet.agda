open import Functional hiding (Domain)
import      Structure.Logic.Classical.NaturalDeduction
import      Structure.Logic.Classical.SetTheory.ZFC

module Structure.Logic.Classical.SetTheory.ZFC.BinaryRelatorSet {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) ⦃ signature : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)
open Structure.Logic.Classical.SetTheory.ZFC.Signature {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ {_∈_} (signature)

open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)

-- Like:
--   (x,f(x)) = (x , y)
--   f = {(x , y)}
--   = {{{x},{x,y}}}
--   ⋃f = {{x},{x,y}}
--   ⋃²f = {x,y}
lefts : Domain → Domain
lefts(s) = filter(⋃(⋃ s)) (x ↦ ∃ₗ(y ↦ (x , y) ∈ s))

rights : Domain → Domain
rights(s) = filter(⋃(⋃ s)) (y ↦ ∃ₗ(x ↦ (x , y) ∈ s))

leftsOfMany : Domain → Domain → Domain
leftsOfMany f(S) = filter(⋃(⋃ f)) (a ↦ ∃ₛ(S)(y ↦ (a , y) ∈ f))

rightsOfMany : Domain → Domain → Domain
rightsOfMany f(S) = filter(⋃(⋃ f)) (a ↦ ∃ₛ(S)(x ↦ (x , a) ∈ f))

leftsOf : Domain → Domain → Domain
leftsOf f(y) = leftsOfMany f(singleton(y))

rightsOf : Domain → Domain → Domain
rightsOf f(x) = rightsOfMany f(singleton(x))

-- swap : Domain → Domain
-- swap(s) = filter(rights(s) ⨯ left(s)) (xy ↦ )
