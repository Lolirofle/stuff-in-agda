module Structure.Category.Functor.Category where

open import Data.Tuple
open import Function.Equals
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.Equiv
import      Structure.Category.NaturalTransformation.NaturalTransformations
open        Structure.Category.NaturalTransformation.NaturalTransformations.Wrapped
open import Structure.Categorical.Properties
open import Structure.Operator
open import Syntax.Transitivity
open import Type

module _
  {ℓₗₒ ℓₗₘ ℓₗₑ ℓᵣₒ ℓᵣₘ ℓᵣₑ}
  (A : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ})
  (B : CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ})
  where

  open CategoryObject ⦃ … ⦄
  private open module MorphismEquivₗ {x}{y} = Equiv(CategoryObject.morphism-equiv A {x}{y}) using ()
  private open module MorphismEquivᵣ {x}{y} = Equiv(CategoryObject.morphism-equiv B {x}{y}) using ()
  private instance _ = A
  private instance _ = B

  -- Functors (as objects) and natural transformations (as morphisms) between them form a category.
  functorCategory : Category{Obj = A →ᶠᵘⁿᶜᵗᵒʳ B} (_→ᴺᵀ_)
  Category._∘_ functorCategory = _∘ᴺᵀ_
  Category.id  functorCategory = idᴺᵀ
  Dependent._⊜_.proof (BinaryOperator.congruence (Category.binaryOperator functorCategory) (Dependent.intro xy1) (Dependent.intro xy2)) = congruence₂(_∘_) xy1 xy2
  Dependent._⊜_.proof (Morphism.Associativity.proof (Category.associativity functorCategory)) = Morphism.associativity(_∘_)
  Dependent._⊜_.proof (Morphism.Identityₗ.proof (left (Category.identity functorCategory)) {F₁} {F₂} {ηᴺᵀ}) {x} =
    ∃.witness (idᴺᵀ ∘ᴺᵀ ηᴺᵀ)(x)                   🝖[ _≡_ ]-[]
    ∃.witness(idᴺᵀ{F = F₂})(x) ∘ ∃.witness ηᴺᵀ(x) 🝖[ _≡_ ]-[]
    id ∘ ∃.witness ηᴺᵀ(x)                         🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    ∃.witness ηᴺᵀ(x)                              🝖-end
  Dependent._⊜_.proof (Morphism.Identityᵣ.proof (right (Category.identity functorCategory)) {F₁} {F₂} {ηᴺᵀ}) {x} =
    ∃.witness (ηᴺᵀ ∘ᴺᵀ idᴺᵀ)(x)                   🝖[ _≡_ ]-[]
    ∃.witness ηᴺᵀ(x) ∘ ∃.witness(idᴺᵀ{F = F₁})(x) 🝖[ _≡_ ]-[]
    ∃.witness ηᴺᵀ(x) ∘ id                         🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]
    ∃.witness ηᴺᵀ(x)                              🝖-end

  Functorᶜᵃᵗ : CategoryObject
  Functorᶜᵃᵗ = intro functorCategory

module _
  {ℓₒ ℓₘ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ})
  where

  Endofunctorᶜᵃᵗ : CategoryObject
  Endofunctorᶜᵃᵗ = Functorᶜᵃᵗ(C)(C)
