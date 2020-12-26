open import Structure.Setoid.WithLvl
open import Structure.Category
open import Type

module Structure.Category.Monad.ExtensionSystem
  {ℓₒ ℓₘ ℓₑ}
  {cat : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}}
  where

import      Data.Tuple as Tuple
import      Function.Equals
open        Function.Equals.Dependent
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic.Predicate
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
open import Structure.Category.Monad{cat = cat}
open import Structure.Category.NaturalTransformation
open import Structure.Category.NaturalTransformation.NaturalTransformations as NaturalTransformations
open import Structure.Category.Proofs
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity

open CategoryObject(cat)
open Category.ArrowNotation(category)
open Category(category)
open NaturalTransformations.Raw(cat)(cat)
private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

record ExtensionSystem (T : Object → Object) : Type{Lvl.of(Type.of(cat))} where
  field
    η   : (x : Object) → (x ⟶ T(x))
    ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))

  μ : (x : Object) → (T(T(x)) ⟶ T(x))
  μ(x) = ext(id{x = T(x)})

  field
    ⦃ ext-function ⦄ : ∀{x y} → Function(ext{x}{y})
    ext-inverse      : ∀{x} → (ext(η(x)) ≡ id) -- ext ∘ᶠⁿ η ⊜ idᴺᵀ
    ext-identity     : ∀{x y}{f : x ⟶ T(y)} → (ext(f) ∘ η(x) ≡ f)
    ext-distribute   : ∀{x y z}{f : y ⟶ T(z)}{g : x ⟶ T(y)} → (ext(ext(f) ∘ g) ≡ ext(f) ∘ ext(g))

  functor : Functor(category)(category)(T)
  Functor.map functor {x} {y} f = ext(η(y) ∘ f)
  Function.congruence (Functor.map-function functor) xy = congruence₁(ext) (congruence₂ᵣ(_∘_)(_) xy)
  Functor.op-preserving functor {x} {y} {z} {f} {g} =
    ext(η(z) ∘ f ∘ g)               🝖-[ congruence₁(ext) (Morphism.associativity(_∘_)) ]-sym
    ext((η(z) ∘ f) ∘ g)             🝖-[ congruence₁(ext) (congruence₂ₗ(_∘_)(g) (symmetry(_≡_) ext-identity)) ]
    ext((ext(η(z) ∘ f) ∘ η(y)) ∘ g) 🝖-[ congruence₁(ext) (Morphism.associativity(_∘_)) ]
    ext(ext(η(z) ∘ f) ∘ (η(y) ∘ g)) 🝖-[ ext-distribute ]
    ext(η(z) ∘ f) ∘ ext(η(y) ∘ g)   🝖-end
  Functor.id-preserving functor {x} =
    ext(η(x) ∘ id) 🝖-[ congruence₁(ext) (Morphism.identityᵣ(_∘_)(id)) ]
    ext(η(x))      🝖-[ ext-inverse ]
    id             🝖-end
  open Functor(functor)

  monad : Monad(T) ⦃ functor ⦄
  ∃.witness (Monad.Η monad) = η
  NaturalTransformation.natural (∃.proof (Monad.Η monad)) = symmetry(_≡_) ext-identity
  ∃.witness (Monad.Μ monad) = μ
  NaturalTransformation.natural (∃.proof (Monad.Μ monad)) {x} {y} {f} =
    μ(y) ∘ ext(η(T(y)) ∘ ext(η(y) ∘ f))      🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(y)) ∘ ext(η(y) ∘ f))   🝖-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(y)) ∘ ext(η(y) ∘ f))) 🝖-[ congruence₁(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(y))) ∘ ext(η(y) ∘ f)) 🝖-[ congruence₁(ext) (congruence₂ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ ext(η(y) ∘ f))                  🝖-[ congruence₁(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(ext(η(y) ∘ f))                       🝖-[ congruence₁(ext) (Morphism.identityᵣ(_∘_)(id)) ]-sym
    ext(ext(η(y) ∘ f) ∘ id)                  🝖-[ ext-distribute ]
    ext(η(y) ∘ f) ∘ ext(id)                  🝖[ _≡_ ]-[]
    ext(η(y) ∘ f) ∘ μ(x)                     🝖-end
  _⊜_.proof (Monad.μ-functor-[∘]-commutativity monad) {x} = -- TODO: Same as above?
    μ(x) ∘ map(μ(x))                   🝖[ _≡_ ]-[]
    ext(id) ∘ map(ext(id))             🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(x)) ∘ ext(id))   🝖-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(x)) ∘ ext(id))) 🝖-[ congruence₁(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(x))) ∘ ext(id)) 🝖-[ congruence₁(ext) (congruence₂ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ ext(id))                  🝖-[ congruence₁(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(ext(id))                       🝖-[ congruence₁(ext) (Morphism.identityᵣ(_∘_)(id)) ]-sym
    ext(ext(id) ∘ id)                  🝖-[ ext-distribute ]
    ext(id) ∘ ext(id)                  🝖[ _≡_ ]-[]
    μ(x) ∘ μ(T(x))                     🝖-end
  _⊜_.proof (Monad.μ-functor-[∘]-identityₗ monad) {x} =
    μ(x) ∘ ext(η(T(x)) ∘ η(x))      🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(x)) ∘ η(x))   🝖[ _≡_ ]-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(x)) ∘ η(x))) 🝖[ _≡_ ]-[ congruence₁(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(x))) ∘ η(x)) 🝖[ _≡_ ]-[ congruence₁(ext) (congruence₂ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ η(x))                  🝖[ _≡_ ]-[ congruence₁(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(η(x))                       🝖[ _≡_ ]-[ ext-inverse ]
    id                              🝖[ _≡_ ]-end
  _⊜_.proof (Monad.μ-functor-[∘]-identityᵣ monad) {x} =
    μ(x) ∘ η(T(x))    🝖[ _≡_ ]-[]
    ext(id) ∘ η(T(x)) 🝖[ _≡_ ]-[ ext-identity ]
    id                🝖[ _≡_ ]-end

  -- Also called: Kleisli composition.
  _∘ₑₓₜ_ : ∀{x y z} → (y ⟶ T(z)) → (x ⟶ T(y)) → (x ⟶ T(z))
  f ∘ₑₓₜ g = ext(f) ∘ g

  idₑₓₜ : ∀{x} → (x ⟶ T(x))
  idₑₓₜ{x} = η(x)

  {-
  categoryₑₓₜ : Category(\x y → (x ⟶ T(y)))
  Category._∘_ categoryₑₓₜ = _∘ₑₓₜ_
  Category.id categoryₑₓₜ = idₑₓₜ
  BinaryOperator.congruence (Category.binaryOperator categoryₑₓₜ) xy1 xy2 = {!!}
  Morphism.Associativity.proof (Category.associativity categoryₑₓₜ) = {!ext-distribute!}
  Morphism.Identityₗ.proof (Tuple.left (Category.identity categoryₑₓₜ)) = {!ext-distribute!}
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity categoryₑₓₜ)) = ext-identity
  -}

  module FunctionalNames where
    lift : ∀{x} → (x ⟶ T(x))
    lift{x} = η(x)

    flatten : ∀{x} → (T(T(x)) ⟶ T(x))
    flatten{x} = μ(x)

    flatMap : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))
    flatMap = ext

  module HaskellNames where
    return = FunctionalNames.lift
    join   = FunctionalNames.flatten
    bind   = FunctionalNames.flatMap

module _ where
  open Functor ⦃ … ⦄
  open Monad   ⦃ … ⦄

  monad-to-extensionSystem : ∀{T : Object → Object} → ⦃ functor : Functor(category)(category)(T) ⦄ → ⦃ monad : Monad(T) ⦄ → ExtensionSystem(T)
  ExtensionSystem.η   (monad-to-extensionSystem ⦃ functor ⦄ ⦃ monad ⦄) = η
  ExtensionSystem.ext (monad-to-extensionSystem ⦃ functor ⦄ ⦃ monad ⦄) = ext
  Function.congruence (ExtensionSystem.ext-function monad-to-extensionSystem  {x} {y}) {f} {g} fg =
    ((μ(y) ∘_) ∘ᶠⁿ map) f 🝖[ _≡_ ]-[]
    μ(y) ∘ map f          🝖[ _≡_ ]-[ congruence₂ᵣ(_∘_) _ (congruence₁(map) fg) ]
    μ(y) ∘ map g          🝖[ _≡_ ]-[]
    ((μ(y) ∘_) ∘ᶠⁿ map) g 🝖[ _≡_ ]-end
  ExtensionSystem.ext-inverse monad-to-extensionSystem {x} =
    ((μ(x) ∘_) ∘ᶠⁿ map)(η(x)) 🝖[ _≡_ ]-[]
    μ(x) ∘ map(η(x))          🝖[ _≡_ ]-[ _⊜_.proof μ-functor-[∘]-identityₗ ]
    id                        🝖[ _≡_ ]-end
  ExtensionSystem.ext-identity (monad-to-extensionSystem {T = T}) {x} {y} {f} =
    ((μ(y) ∘_) ∘ᶠⁿ map)(f) ∘ η(x) 🝖[ _≡_ ]-[]
    (μ(y) ∘ (map f)) ∘ η(x)       🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
    μ(y) ∘ ((map f) ∘ η(x))       🝖[ _≡_ ]-[ congruence₂ᵣ(_∘_) _ η-natural ]-sym
    μ(y) ∘ (η(T(y)) ∘ f)          🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
    (μ(y) ∘ η(T(y))) ∘ f          🝖[ _≡_ ]-[ congruence₂ₗ(_∘_) _ (_⊜_.proof μ-functor-[∘]-identityᵣ) ]
    id ∘ f                        🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]    
    f                             🝖[ _≡_ ]-end
  ExtensionSystem.ext-distribute (monad-to-extensionSystem {T = T}) {x} {y} {z} {f} {g} =
    ((μ(z) ∘_) ∘ᶠⁿ map)(((μ(z) ∘_) ∘ᶠⁿ map)(f) ∘ g) 🝖[ _≡_ ]-[]
    μ(z) ∘ map((μ(z) ∘ (map f)) ∘ g)                🝖[ _≡_ ]-[ congruence₂ᵣ(_∘_) _ op-preserving ]
    μ(z) ∘ (map(μ(z) ∘ (map f)) ∘ (map g))          🝖[ _≡_ ]-[ congruence₂ᵣ(_∘_) _ (congruence₂ₗ(_∘_) _ op-preserving) ]
    μ(z) ∘ ((map(μ(z)) ∘ map(map f)) ∘ (map g))     🝖[ _≡_ ]-[ associate4-231-121 category ]
    (μ(z) ∘ map(μ(z))) ∘ (map(map f) ∘ (map g))     🝖[ _≡_ ]-[ congruence₂ₗ(_∘_) _ (_⊜_.proof μ-functor-[∘]-commutativity) ]
    (μ(z) ∘ μ(T(z))) ∘ (map(map f) ∘ (map g))       🝖[ _≡_ ]-[ associate4-213-121 category ]-sym
    (μ(z) ∘ (μ(T(z)) ∘ map(map f))) ∘ (map g)       🝖[ _≡_ ]-[ congruence₂ₗ(_∘_) _ (congruence₂ᵣ(_∘_) _ μ-natural) ]
    (μ(z) ∘ ((map f) ∘ μ(y))) ∘ (map g)             🝖[ _≡_ ]-[ associate4-213-121 category ]
    (μ(z) ∘ (map f)) ∘ (μ(y) ∘ (map g))             🝖[ _≡_ ]-[]
    ((μ(z) ∘_) ∘ᶠⁿ map)(f) ∘ ((μ(y) ∘_) ∘ᶠⁿ map)(g) 🝖[ _≡_ ]-end
