open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation6 {ℓᵣ ℓ ℓₑ} (Range : Type{ℓᵣ}) {T : Type{ℓ}} (_▫_ : T → T → T) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

open import Functional using (pointwise₂,₁ ; const)
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Signature.IndexedCategory
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Type.Function
open import Syntax.Function

record Foldable {C : IndexedCategory} ⦃ func : FunctionSignature(C) ⦄ ⦃ funcApp : FunctionApplication(C) ⦄ {ℓᵢ ℓₚ} : Type{Lvl.𝐒(ℓᵢ) Lvl.⊔ Lvl.𝐒(ℓₚ) Lvl.⊔ ℓᵣ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  open IndexedCategory(C) using (_⟶_)
  field
    Container : Object → Object
    ∑ : ∀{x y} → (x ⟶ y) → (Container(x) ⟶ y)

  field
    preserves-operator : ⦃ assoc : Associativity(_▫_) ⦄ → ∀{r}{f g} → (∑(r) (pointwise₂,₁(_▫_) f g) ≡ (∑(r) f) ▫ (∑(r) g))
    preserves-identity : ∀{id} ⦃ ident  : Identity(_▫_)(id) ⦄ → ∀{r}{f} → (∀{i : Index(r)} → (f(i) ≡ id)) → (∑(r) f ≡ id)
    preserves-absorber : ∀{ab} ⦃ absorb : Absorber(_▫_)(ab) ⦄ → ∀{r}{f} → ∃(\(i : Index(r)) → (f(i) ≡ ab)) → (∑(r) f ≡ ab)
open Summation ⦃ … ⦄ using (∑) public
