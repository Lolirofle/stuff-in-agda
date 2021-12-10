open import Structure.Category
open import Type

module Structure.Category.Monad.Category
  {ℓₒ ℓₘ ℓₑ}
  {cat : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Data.Tuple as Tuple
import      Function.Equals
open        Function.Equals.Dependent
import      Lvl
open import Structure.Category.Functor
open import Structure.Category.Monad{cat = cat}
open import Structure.Category.Monad.ExtensionSystem{cat = cat}
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Syntax.Transitivity

open CategoryObject(cat)
open Category.ArrowNotation(category)
open Category(category)
private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

module _ (T : Object → Object) ⦃ extSys : ExtensionSystem(T) ⦄ where
  open ExtensionSystem(extSys)
  open Functor(functor)
  open Monad ⦃ functor ⦄ (monad) using (μ-functor-[∘]-identityₗ)

  -- Also called: Kleisli category
  categoryₑₓₜ : Category(\x y → (x ⟶ T(y)))
  Category._∘_ categoryₑₓₜ = _∘ₑₓₜ_
  Category.id  categoryₑₓₜ = idₑₓₜ
  BinaryOperator.congruence (Category.binaryOperator categoryₑₓₜ {x}{y}{z}) {f₁}{f₂} {g₁}{g₂} f₁f₂ g₁g₂ =
    f₁ ∘ₑₓₜ g₁           🝖[ _≡_ ]-[]
    ext f₁ ∘ g₁          🝖[ _≡_ ]-[ congruence₂(_∘_) (congruence₁(ext) f₁f₂) g₁g₂ ]
    ext f₂ ∘ g₂          🝖[ _≡_ ]-[]
    f₂ ∘ₑₓₜ g₂           🝖-end
  Morphism.Associativity.proof (Category.associativity categoryₑₓₜ) {x} {y} {z} {w} {f} {g} {h} =
    (f ∘ₑₓₜ g) ∘ₑₓₜ h     🝖[ _≡_ ]-[]
    ext(ext(f) ∘ g) ∘ h   🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) ext-distribute ]
    (ext(f) ∘ ext(g)) ∘ h 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
    ext(f) ∘ (ext(g) ∘ h) 🝖[ _≡_ ]-[]
    f ∘ₑₓₜ (g ∘ₑₓₜ h)     🝖-end
  Morphism.Identityₗ.proof (Tuple.left (Category.identity categoryₑₓₜ)) {x} {y} {f} =
    idₑₓₜ ∘ₑₓₜ f           🝖[ _≡_ ]-[]
    ext(η(y)) ∘ f          🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(f) ext-inverse ]
    id ∘ f                 🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    f                      🝖-end
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity categoryₑₓₜ)) {x} {y} {f} =
    f ∘ₑₓₜ idₑₓₜ  🝖[ _≡_ ]-[]
    ext(f) ∘ η(x) 🝖[ _≡_ ]-[ ext-identity ]
    f             🝖-end

module _ (T : Object → Object) ⦃ functor : Functor(category)(category)(T) ⦄ ⦃ monad : Monad(T) ⦄ where
  open Functor(functor)
  open Monad(monad) hiding (ext)
  open ExtensionSystem(monad-to-extensionSystem) hiding (η ; μ)

  -- Note: This is the supposed to be the same as categoryₑₓₜ but proven from a monad directly.
  monad-category : Category(\x y → (x ⟶ T(y)))
  Category._∘_ monad-category f g = ext(f) ∘ g
  Category.id monad-category {x} = η(x)
  BinaryOperator.congruence (Category.binaryOperator monad-category {x}{y}{z}) {f₁}{f₂} {g₁}{g₂} f₁f₂ g₁g₂ =
    ext(f₁) ∘ g₁         🝖[ _≡_ ]-[]
    (μ(z) ∘ map f₁) ∘ g₁ 🝖-[ Morphism.associativity(_∘_) ]
    μ(z) ∘ (map f₁ ∘ g₁) 🝖-[ congruence₂-₂(_∘_)(μ(z)) (congruence₂(_∘_) (congruence₁(map) f₁f₂) g₁g₂) ]
    μ(z) ∘ (map f₂ ∘ g₂) 🝖-[ Morphism.associativity(_∘_) ]-sym
    (μ(z) ∘ map f₂) ∘ g₂ 🝖[ _≡_ ]-[]
    ext(f₂) ∘ g₂         🝖-end
  Morphism.Associativity.proof (Category.associativity monad-category) {x} {y} {z} {w} {f} {g} {h} =
    ext(ext(f) ∘ g) ∘ h   🝖-[ congruence₂-₁(_∘_)(_) (ext-distribute) ]
    (ext(f) ∘ ext(g)) ∘ h 🝖-[ Morphism.associativity(_∘_) ]
    ext(f) ∘ (ext(g) ∘ h) 🝖-end
  Morphism.Identityₗ.proof (Tuple.left (Category.identity monad-category)) {x} {y} {f} =
    ext(η(y)) ∘ f          🝖[ _≡_ ]-[]
    (μ(y) ∘ map(η(y))) ∘ f 🝖-[ congruence₂-₁(_∘_)(f) (_⊜_.proof μ-functor-[∘]-identityₗ) ]
    id ∘ f                 🝖-[ Morphism.identityₗ(_∘_)(id) ]
    f                      🝖-end
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity monad-category)) {x} {y} {f} = ext-identity
