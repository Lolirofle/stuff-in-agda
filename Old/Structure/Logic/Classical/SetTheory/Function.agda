open import Functional using (id)
import      Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.Function {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Constructive.Functions(Domain)
open import Structure.Logic.Constructive.Functions.Properties ⦃ constructiveLogicSignature ⦄

-- States whether the function f is defined for all elements in the set X.
Map : Function → Domain → Formula
Map f(X) = ∀ₛ(X) (x ↦ Defined f(x))
