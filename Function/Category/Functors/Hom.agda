import      Function.Equiv as Fn
import      Functional as Fn
open import Structure.Category
open import Structure.Operator
open import Structure.Setoid
open import Type

module Function.Category.Functors.Hom
  {ℓₜ ℓₑₜ}
  ⦃ equiv-func : ∀{A B : Type{ℓₜ}} → Equiv{ℓₑₜ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₜ}} → BinaryOperator(Fn._∘_ {X = A}{Y = B}{Z = C}) ⦄
  {ℓₒ ℓₑ}
  (C : CategoryObject{ℓₒ}{ℓₜ}{ℓₑ})
  ⦃ ext : ∀{x₁ y₁ x₂ y₂ : CategoryObject.Object(C)} → Fn.Extensionality(CategoryObject.morphism-equiv(C) {x₂}{y₂})(equiv-func{CategoryObject.Morphism(C) x₁ y₁}{CategoryObject.Morphism(C) x₂ y₂}) ⦄
  where

open import Logic.Predicate
open import Structure.Category.Dual
open import Structure.Category.Functor
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.IndexedOperator.Properties.Preserving
open import Structure.Relator.Properties
open import Type.Category ⦃ equiv-func ⦄ ⦃ [∘]-func ⦄

open CategoryObject(C)
open Category.ArrowNotation(category)

CovariantHomᶠᵘⁿᶜᵗᵒʳ : Object → (C →ᶠᵘⁿᶜᵗᵒʳ Typeᶜᵃᵗ)
CovariantHomᶠᵘⁿᶜᵗᵒʳ x = [∃]-intro (x ⟶_) where
  instance
    functor : Functor category typeFnCategory (x ⟶_)
    Functor.map           functor = (_∘_)
    Functor.map-function  functor = intro \{f₁}{f₂} f₁f₂ → Fn.functionExtensionality \{g} → congruence₂-₁(_∘_)(g) f₁f₂
    Functor.op-preserving functor = intro(Fn.functionExtensionality(Morphism.associativity(_∘_)))
    Functor.id-preserving functor = intro(Fn.functionExtensionality(Morphism.identityₗ(_∘_)(id)))

ContravariantHomᶠᵘⁿᶜᵗᵒʳ : Object → (dual(C) →ᶠᵘⁿᶜᵗᵒʳ Typeᶜᵃᵗ)
ContravariantHomᶠᵘⁿᶜᵗᵒʳ y = [∃]-intro (_⟶ y) where
  instance
    functor : Functor (dualCategory category) typeFnCategory (_⟶ y)
    Functor.map           functor = Fn.swap(_∘_)
    Functor.map-function  functor = intro \{g₁}{g₂} g₁g₂ → Fn.functionExtensionality \{f} → congruence₂-₂(_∘_)(f) g₁g₂
    Functor.op-preserving functor = intro(Fn.functionExtensionality (symmetry(_) ⦃ Equiv.symmetry morphism-equiv ⦄ (Morphism.associativity(_∘_))))
    Functor.id-preserving functor = intro(Fn.functionExtensionality(Morphism.identityᵣ(_∘_)(id)))



open import Data.Tuple as Tuple using (_,_)
open import Data.Tuple.Category
open import Logic.Propositional
open import Structure.Category.Proofs
open import Syntax.Transitivity

private open module MorphismEquiv{A}{B} = Equiv(morphism-equiv{A}{B}) using ()

Homᶠᵘⁿᶜᵗᵒʳ : Object → ((dual(C) ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ Typeᶜᵃᵗ)
Homᶠᵘⁿᶜᵗᵒʳ y = [∃]-intro (Tuple.uncurry(_⟶_)) ⦃ functor ⦄ where
  instance
    functor : Functor ⦃ _ ⦄ (tupleCategory(dualCategory category) category) typeFnCategory (Tuple.uncurry(_⟶_))
    Functor.map functor = \(r , l) f → l ∘ f ∘ r
    Functor.map-function  functor = intro \{ {r₁ , l₁}{r₂ , l₂} ([∧]-intro pr pl) →
      Fn.functionExtensionality \{f} →
        l₁ ∘ f ∘ r₁ 🝖[ _≡_ ]-[ congruence₂(_∘_) pl (congruence₂-₂(_∘_)(f) pr) ]
        l₂ ∘ f ∘ r₂ 🝖-end
      }
    Functor.op-preserving functor = intro \{ {r₁ , l₁}{r₂ , l₂} →
      Fn.functionExtensionality \{f} →
        (l₁ ∘ l₂) ∘ f ∘ (r₂ ∘ r₁)   🝖[ _≡_ ]-[]
        (l₁ ∘ l₂) ∘ (f ∘ (r₂ ∘ r₁)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
        l₁ ∘ (l₂ ∘ (f ∘ (r₂ ∘ r₁))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(l₁) (associate4-321-213 category) ]
        l₁ ∘ ((l₂ ∘ (f ∘ r₂)) ∘ r₁) 🝖[ _≡_ ]-[]
        l₁ ∘ (l₂ ∘ f ∘ r₂) ∘ r₁     🝖-end
      }
    Functor.id-preserving functor = intro Fn.$ Fn.functionExtensionality \{f} →
      id ∘ (f ∘ id) 🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
      f ∘ id        🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]
      f             🝖-end
