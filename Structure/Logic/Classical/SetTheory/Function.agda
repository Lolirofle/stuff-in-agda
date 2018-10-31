import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.Function {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign : _ ⦄ ⦃ theory : _ ⦄ (_∈_ : Domain → Domain → Formula) where
private module PredicateEq = Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₒ} {Object} (obj)
open PredicateEq.Signature(sign)
open PredicateEq.Theory(theory)

open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign ⦄ ⦃ theory ⦄ (_∈_)

-- States whether the function f is defined for all elements in the set X.
Map : Function → Domain → Formula
Map f(X) = ∀ₛ(X) (Defined(f))
