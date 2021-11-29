module Structure.Operator.Vector.LinearMap.Category where

import      Data.Tuple as Tuple
open import Functional
open import Function.Proofs
open import Function.Equals
open import Function.Equals.Proofs
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Logic.Propositional
import      Lvl
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.LinearMaps as LinearMaps using (_∘ˡⁱⁿᵉᵃʳᵐᵃᵖ_ ; idˡⁱⁿᵉᵃʳᵐᵃᵖ)
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓᵥ₁ ℓᵥ₂ ℓᵥ₃ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ ℓₙ₀ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable f g : Vₗ → Vᵣ

open VectorSpace ⦃ … ⦄
open VectorSpaceVObject

module _ ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ {_+ₛ_ _⋅ₛ_ : S → S → S} where
  private variable A B : VectorSpaceVObject {ℓᵥ}{_}{ℓᵥₑ}{ℓₛₑ} ⦃ equiv-S ⦄ (_+ₛ_)(_⋅ₛ_) {ℓₙ₀}

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-reflexivity : Reflexivity(_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_})
    ∃.witness (Reflexivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-reflexivity) = id
    Tuple.left (∃.proof (Reflexivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-reflexivity)) = {!!}
    Tuple.right (∃.proof (Reflexivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-reflexivity {V})) = LinearMaps.identity (VectorSpaceVObject.vectorSpace V)

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-symmetry : Symmetry(_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_})
    ∃.witness (Symmetry.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-symmetry ([∃]-intro f ⦃ [∧]-intro p q ⦄)) = {!!}
    Tuple.left (∃.proof (Symmetry.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-symmetry x)) = {!!}
    Tuple.right (∃.proof (Symmetry.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-symmetry x)) = {!!}

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-transitivity : Transitivity(_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_})
    ∃.witness (Transitivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-transitivity ([∃]-intro f) ([∃]-intro g)) = g ∘ f
    Tuple.left (∃.proof (Transitivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-transitivity p q)) = {!!}
    Tuple.right (∃.proof (Transitivity.proof [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-transitivity {V₁}{V₂}{V₃} ([∃]-intro _ ⦃ p ⦄) ([∃]-intro _ ⦃ q ⦄))) = LinearMaps.compose (VectorSpaceVObject.vectorSpace V₁)(VectorSpaceVObject.vectorSpace V₂)(VectorSpaceVObject.vectorSpace V₃) (Tuple.right q) (Tuple.right p)

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equivalence : Equivalence(_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_})
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equivalence = intro

  instance
    VectorSpaceVObject-equiv : Equiv(VectorSpaceVObject{ℓᵥ = ℓᵥ}{ℓᵥₑ = ℓᵥₑ}(_+ₛ_)(_⋅ₛ_))
    Equiv._≡_ VectorSpaceVObject-equiv = _↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_
    Equiv.equivalence VectorSpaceVObject-equiv = [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equivalence

  instance
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv : Equiv(A →ˡⁱⁿᵉᵃʳᵐᵃᵖ B)
    [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv {A = A} {B = B} = [≡∃]-equiv ⦃ [⊜]-equiv ⦃ Vector-equiv B ⦄ ⦄

  -- Equiv._≡_ [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv ([∃]-intro f) ([∃]-intro g) = {!!}
  -- Equiv.equivalence [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv = {!!}

  linearMapCategory : Category(_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_ {ℓᵥₗ = ℓᵥₗ}{ℓᵥₑₗ = ℓᵥₑₗ}{_+ₛ_ = _+ₛ_}{_⋅ₛ_ = _⋅ₛ_}) ⦃ [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv ⦄
  Category._∘_ linearMapCategory = _∘ˡⁱⁿᵉᵃʳᵐᵃᵖ_
  Category.id  linearMapCategory = idˡⁱⁿᵉᵃʳᵐᵃᵖ
  BinaryOperator.congruence (Category.binaryOperator linearMapCategory) p q = [⊜][∘]-binaryOperator-raw p q
  Morphism.Associativity.proof (Category.associativity linearMapCategory) {X}{Y}{Z}{W} = intro(reflexivity(Equiv._≡_ (Vector-equiv(W))))
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity linearMapCategory)) {X}{Y} = intro(reflexivity(Equiv._≡_ (Vector-equiv(Y))))
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity linearMapCategory)) {X}{Y} = intro(reflexivity(Equiv._≡_ (Vector-equiv(Y))))

-- _≡∃_ {Obj = {!!}} ⦃ {![⊜]-equiv ⦃ Vector-equiv Y ⦄!} ⦄ {Pred = {!f ↦ LinearMap(vectorSpace(X))(vectorSpace(Y)) (f)!}}
