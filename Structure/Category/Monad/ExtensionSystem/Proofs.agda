open import Structure.Category
open import Type

module Structure.Category.Monad.ExtensionSystem.Proofs
  {ℓₒ ℓₘ ℓₑ}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Functional as Fn
import      Function.Equals
open        Function.Equals.Dependent
open import DependentFunctional using () renaming (_∘_ to _∘ᶠⁿ_)
open import Logic.Predicate
open import Structure.Category.Functor
open import Structure.Category.Monad{C = C}
open import Structure.Category.Monad.ExtensionSystem {ℓₒ}{ℓₘ}{ℓₑ}{C}
open import Structure.Category.NaturalTransformation
open import Structure.Category.Proofs
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity

open CategoryObject(C)
open Category.ArrowNotation(category)
private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

module _ {T : Object → Object} ⦃ extT : ExtensionSystem(T) ⦄ where
  open ExtensionSystem(extT)

  functor : Functor(category)(category)(T)
  Functor.map functor {x} {y} f = ext(η(y) ∘ f)
  Function.congruence (Functor.map-function functor) xy = congruence₁(ext) (congruence₂-₂(_∘_)(_) xy)
  Functor.op-preserving functor {x}{y}{z} = intro \{f}{g} →
    ext(η(z) ∘ f ∘ g)               🝖-[ congruence₁(ext) (Morphism.associativity(_∘_)) ]-sym
    ext((η(z) ∘ f) ∘ g)             🝖-[ congruence₁(ext) (congruence₂-₁(_∘_)(g) (symmetry(_≡_) ext-identity)) ]
    ext((ext(η(z) ∘ f) ∘ η(y)) ∘ g) 🝖-[ congruence₁(ext) (Morphism.associativity(_∘_)) ]
    ext(ext(η(z) ∘ f) ∘ (η(y) ∘ g)) 🝖-[ ext-distribute ]
    ext(η(z) ∘ f) ∘ ext(η(y) ∘ g)   🝖-end
  Functor.id-preserving functor {x} = intro Fn.$
    ext(η(x) ∘ id) 🝖-[ congruence₁(ext) (Morphism.identityᵣ(_∘_)(id)) ]
    ext(η(x))      🝖-[ ext-inverse ]
    id             🝖-end
  open Functor(functor)

  ext-η-composeᵣ-to-ext : ∀{x y}{f : x ⟶ T(y)} → (μ(y) ∘ ext(η(T(y)) ∘ f) ≡ ext(f))
  ext-η-composeᵣ-to-ext{x}{y}{f} =
    μ(y) ∘ (ext(η(T(y)) ∘ f))    🝖[ _≡_ ]-[]
    ext(id) ∘ (ext(η(T(y)) ∘ f)) 🝖[ _≡_ ]-[ ext-distribute ]-sym
    ext(μ(y) ∘ (η(T(y)) ∘ f))    🝖[ _≡_ ]-[ congruence₁(ext) Fn.$
      μ(y) ∘ (η(T(y)) ∘ f)    🝖[ _≡_ ]-[]
      ext(id) ∘ (η(T(y)) ∘ f) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (ext(id) ∘ η(T(y))) ∘ f 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) ext-identity ]
      id ∘ f                  🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
      f                       🝖[ _≡_ ]-end
    ]
    ext(f)                       🝖[ _≡_ ]-end

  nested-ext-is-ext-μ : ∀{x y}{f : x ⟶ T(y)} → (ext(ext(f)) ≡ ext(f) ∘ μ(x))
  nested-ext-is-ext-μ {x}{y}{f} =
    ext(ext(f))      🝖[ _≡_ ]-[ congruence₁(ext) (Morphism.identityᵣ(_∘_)(id)) ]-sym
    ext(ext(f) ∘ id) 🝖[ _≡_ ]-[ ext-distribute ]
    ext(f) ∘ ext(id) 🝖[ _≡_ ]-[]
    ext(f) ∘ μ(x)    🝖[ _≡_ ]-end

  monad : Monad([∃]-intro T ⦃ functor ⦄)
  ∃.witness (Monad.Η monad) = η
  NaturalTransformation.natural (∃.proof (Monad.Η monad)) = symmetry(_≡_) ext-identity
  ∃.witness (Monad.Μ monad) = μ
  NaturalTransformation.natural (∃.proof (Monad.Μ monad)) {x} {y} {f} =
    μ(y) ∘ ext(η(T(y)) ∘ ext(η(y) ∘ f)) 🝖[ _≡_ ]-[ ext-η-composeᵣ-to-ext ]
    ext(ext(η(y) ∘ f))                  🝖[ _≡_ ]-[ nested-ext-is-ext-μ ]
    ext(η(y) ∘ f) ∘ μ(x)                🝖-end
  _⊜_.proof (Monad.μ-on-μ-preserving-functor monad) {x} = -- Note: Proof is similar to above.
    μ(x) ∘ map(μ(x))              🝖[ _≡_ ]-[]
    μ(x) ∘ map(ext(id))           🝖[ _≡_ ]-[]
    μ(x) ∘ ext(η(T(x)) ∘ ext(id)) 🝖[ _≡_ ]-[ ext-η-composeᵣ-to-ext ]
    ext(ext(id))                  🝖[ _≡_ ]-[ nested-ext-is-ext-μ ]
    ext(id) ∘ μ(T(x))             🝖[ _≡_ ]-[]
    μ(x) ∘ μ(T(x))                🝖-end
  _⊜_.proof (Monad.μ-on-μ-functor-η-inverse₁ monad) {x} =
    μ(x) ∘ ext(η(T(x)) ∘ η(x))   🝖[ _≡_ ]-[ ext-η-composeᵣ-to-ext ]
    ext(η(x))                    🝖[ _≡_ ]-[ ext-inverse ]
    id                           🝖[ _≡_ ]-end
  _⊜_.proof (Monad.μ-on-μ-functor-η-inverse₀ monad) {x} =
    μ(x) ∘ η(T(x))    🝖[ _≡_ ]-[]
    ext(id) ∘ η(T(x)) 🝖[ _≡_ ]-[ ext-identity ]
    id                🝖[ _≡_ ]-end

module _ where
  open Functor ⦃ … ⦄
  open Monad   ⦃ … ⦄

  monad-to-extensionSystem : ∀{Tᶠᵘⁿᶜᵗᵒʳ@([∃]-intro T) : C →ᶠᵘⁿᶜᵗᵒʳ C} → ⦃ monad : Monad(Tᶠᵘⁿᶜᵗᵒʳ) ⦄ → ExtensionSystem(T)
  ExtensionSystem.η   (monad-to-extensionSystem ⦃ monad ⦄) = η
  ExtensionSystem.ext (monad-to-extensionSystem ⦃ monad ⦄) = ext
  Function.congruence (ExtensionSystem.ext-function monad-to-extensionSystem  {x} {y}) {f} {g} fg =
    ((μ(y) ∘_) ∘ᶠⁿ map) f 🝖[ _≡_ ]-[]
    μ(y) ∘ map f          🝖[ _≡_ ]-[ congruence₂-₂(_∘_) _ (congruence₁(map) fg) ]
    μ(y) ∘ map g          🝖[ _≡_ ]-[]
    ((μ(y) ∘_) ∘ᶠⁿ map) g 🝖[ _≡_ ]-end
  ExtensionSystem.ext-inverse monad-to-extensionSystem {x} =
    ((μ(x) ∘_) ∘ᶠⁿ map)(η(x)) 🝖[ _≡_ ]-[]
    μ(x) ∘ map(η(x))          🝖[ _≡_ ]-[ _⊜_.proof μ-on-μ-functor-η-inverse₁ ]
    id                        🝖[ _≡_ ]-end
  ExtensionSystem.ext-identity (monad-to-extensionSystem {Tᶠᵘⁿᶜᵗᵒʳ = [∃]-intro T}) {x} {y} {f} =
    ((μ(y) ∘_) ∘ᶠⁿ map)(f) ∘ η(x) 🝖[ _≡_ ]-[]
    (μ(y) ∘ (map f)) ∘ η(x)       🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
    μ(y) ∘ ((map f) ∘ η(x))       🝖[ _≡_ ]-[ congruence₂-₂(_∘_) _ η-natural ]-sym
    μ(y) ∘ (η(T(y)) ∘ f)          🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
    (μ(y) ∘ η(T(y))) ∘ f          🝖[ _≡_ ]-[ congruence₂-₁(_∘_) _ (_⊜_.proof μ-on-μ-functor-η-inverse₀) ]
    id ∘ f                        🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]
    f                             🝖[ _≡_ ]-end
  ExtensionSystem.ext-distribute (monad-to-extensionSystem {Tᶠᵘⁿᶜᵗᵒʳ = [∃]-intro T}) {x} {y} {z} {f} {g} =
    ((μ(z) ∘_) ∘ᶠⁿ map)(((μ(z) ∘_) ∘ᶠⁿ map)(f) ∘ g) 🝖[ _≡_ ]-[]
    μ(z) ∘ map((μ(z) ∘ (map f)) ∘ g)                🝖[ _≡_ ]-[ congruence₂-₂(_∘_) _ (preserving₂ _ _ _ _ _ ⦃ op-preserving ⦄) ]
    μ(z) ∘ (map(μ(z) ∘ (map f)) ∘ (map g))          🝖[ _≡_ ]-[ congruence₂-₂(_∘_) _ (congruence₂-₁(_∘_) _ (preserving₂ _ _ _ _ _ ⦃ op-preserving ⦄)) ]
    μ(z) ∘ ((map(μ(z)) ∘ map(map f)) ∘ (map g))     🝖[ _≡_ ]-[ associate4-231-121 category ]
    (μ(z) ∘ map(μ(z))) ∘ (map(map f) ∘ (map g))     🝖[ _≡_ ]-[ congruence₂-₁(_∘_) _ (_⊜_.proof μ-on-μ-preserving-functor) ]
    (μ(z) ∘ μ(T(z))) ∘ (map(map f) ∘ (map g))       🝖[ _≡_ ]-[ associate4-213-121 category ]-sym
    (μ(z) ∘ (μ(T(z)) ∘ map(map f))) ∘ (map g)       🝖[ _≡_ ]-[ congruence₂-₁(_∘_) _ (congruence₂-₂(_∘_) _ μ-natural) ]
    (μ(z) ∘ ((map f) ∘ μ(y))) ∘ (map g)             🝖[ _≡_ ]-[ associate4-213-121 category ]
    (μ(z) ∘ (map f)) ∘ (μ(y) ∘ (map g))             🝖[ _≡_ ]-[]
    ((μ(z) ∘_) ∘ᶠⁿ map)(f) ∘ ((μ(y) ∘_) ∘ᶠⁿ map)(g) 🝖[ _≡_ ]-end
