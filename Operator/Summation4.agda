open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation4 {ℓᵣ ℓ ℓₑ} (Range : Type{ℓᵣ}) {T : Type{ℓ}} (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

open import Functional using (pointwise₂,₁ ; const)
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Signature.IndexedCategory
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Type.Function
open import Syntax.Function

record Summation {C : IndexedCategory} ⦃ func : FunctionSignature(C) ⦄ ⦃ funcApp : FunctionApplication(C) ⦄ ⦃ assoc : Associativity(_▫_) ⦄ {ℓᵢ ℓₚ} : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  open IndexedCategory(C) using (_⟶_)
  field
    Index : Range → Type{ℓᵢ}
    ∑ : (r : Range) → (f : Index(r) ⟶ T) → T

  field
    preserves-operator : ∀{r}{f g} → (∑(r) (pointwise₂,₁(_▫_) f g) ≡ (∑(r) f) ▫ (∑(r) g))
    preserves-identity : ∀{id} ⦃ ident  : Identity(_▫_)(id) ⦄ → ∀{r}{f} → (∀{i : Index(r)} → (f(i) ≡ id)) → (∑(r) f ≡ id)
    preserves-absorber : ∀{ab} ⦃ absorb : Absorber(_▫_)(ab) ⦄ → ∀{r}{f} → ∃(\(i : Index(r)) → (f(i) ≡ ab)) → (∑(r) f ≡ ab)
open Summation ⦃ … ⦄ using (∑) public
