module Structure.Operator.Vector.LinearMap.Category where

import      Data.Tuple as Tuple
open import Functional
open import Function.Proofs
open import Function.Equals
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Logic.Propositional
import      Lvl
open import Structure.Category
open import Structure.Category.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.LinearMaps
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓᵥ₁ ℓᵥ₂ ℓᵥ₃ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable f g : Vₗ → Vᵣ

open VectorSpace ⦃ … ⦄
open VectorSpaceVObject

module _ ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ {_+ₛ_ _⋅ₛ_ : S → S → S} where
  private variable A B : VectorSpaceVObject {ℓᵥ}{_}{ℓᵥₑ}{ℓₛₑ} ⦃ equiv-S ⦄ (_+ₛ_)(_⋅ₛ_)

  instance
    VectorSpaceVObject-equiv : Equiv(VectorSpaceVObject{ℓᵥ = ℓᵥ}{ℓᵥₑ = ℓᵥₑ}(_+ₛ_)(_⋅ₛ_))
    Equiv._≡_ VectorSpaceVObject-equiv = _↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_
    Equiv.equivalence VectorSpaceVObject-equiv = {!!}

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv : Equiv(A →ˡⁱⁿᵉᵃʳᵐᵃᵖ B)
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv {A = A} {B = B} = [≡∃]-equiv ⦃ [⊜]-equiv ⦃ Vector-equiv B ⦄ ⦄
    
  -- Equiv._≡_ [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv ([∃]-intro f) ([∃]-intro g) = {!!}
  -- Equiv.equivalence [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv = {!!}

  linearMapCategory : Category(_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_}) ⦃ \{A B} → [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv {A = A} {B = B} ⦄
  Category._∘_ linearMapCategory = _∘ˡⁱⁿᵉᵃʳᵐᵃᵖ_
  Category.id  linearMapCategory = idˡⁱⁿᵉᵃʳᵐᵃᵖ
  BinaryOperator.congruence (Category.binaryOperator linearMapCategory) x x₁ = {!!}
  Dependent._⊜_.proof (Morphism.Associativity.proof (Category.associativity linearMapCategory) {X} {Y} {Z}) {x} = ?
  -- intro(transitivity(Equiv._≡_ (Vector-equiv(Y))))
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity linearMapCategory)) {X}{Y} = intro(reflexivity(Equiv._≡_ (Vector-equiv(Y))))
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity linearMapCategory)) {X}{Y} = intro(reflexivity(Equiv._≡_ (Vector-equiv(Y))))

-- _≡∃_ {Obj = {!!}} ⦃ {![⊜]-equiv ⦃ Vector-equiv Y ⦄!} ⦄ {Pred = {!f ↦ LinearMap(vectorSpace(X))(vectorSpace(Y)) (f)!}}
