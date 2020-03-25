open import Sets.Setoid
open import Structure.Category
open import Type

module Structure.Category.Monad.ExtensionSystem
  {ℓₒ ℓₘ}
  {Obj : Type{ℓₒ}}
  ⦃ obj-equiv : Equiv(Obj) ⦄
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  {cat : Category(Morphism)}
  where

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
open import Structure.Category.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity

open Category.ArrowNotation(cat)
open Category(cat)
open NaturalTransformations.Raw(cat)(cat)
private instance _ = cat
private open module MorphismEquiv {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

record ExtensionSystem (T : Obj → Obj) : Type{Lvl.of(type-of(cat))} where
  field
    η   : (x : Obj) → (x ⟶ T(x))
    ext : ∀{x y} → (x ⟶ T(y)) → (T(x) ⟶ T(y))

  μ : (x : Obj) → (T(T(x)) ⟶ T(x))
  μ(x) = ext(id{x = T(x)})

  field
    ⦃ function ⦄     : Function(T)
    ⦃ ext-function ⦄ : ∀{x y} → Function(ext{x}{y})
    ext-inverse      : ∀{x} → (ext(η(x)) ≡ id) -- ext ∘ᶠⁿ η ⊜ idᴺᵀ
    ext-identity     : ∀{x y}{f : x ⟶ T(y)} → (ext(f) ∘ η(x) ≡ f)
    ext-distribute   : ∀{x y z}{f : y ⟶ T(z)}{g : x ⟶ T(y)} → (ext(ext(f) ∘ g) ≡ ext(f) ∘ ext(g))

  functor : Functor(cat)(cat)(T)
  Functor.map functor {x} {y} f = ext(η(y) ∘ f)
  Function.congruence (Functor.map-function functor) xy = [≡]-with(ext) ([≡]-with2ᵣ(_∘_)(_) xy)
  Functor.op-preserving functor {x} {y} {z} {f} {g} =
    ext(η(z) ∘ f ∘ g)               🝖-[ [≡]-with(ext) (Morphism.associativity(_∘_)) ]-sym
    ext((η(z) ∘ f) ∘ g)             🝖-[ [≡]-with(ext) ([≡]-with2ₗ(_∘_)(g) (symmetry(_≡_) ext-identity)) ]
    ext((ext(η(z) ∘ f) ∘ η(y)) ∘ g) 🝖-[ [≡]-with(ext) (Morphism.associativity(_∘_)) ]
    ext(ext(η(z) ∘ f) ∘ (η(y) ∘ g)) 🝖-[ ext-distribute ]
    ext(η(z) ∘ f) ∘ ext(η(y) ∘ g)   🝖-end
  Functor.id-preserving functor {x} =
    ext(η(x) ∘ id) 🝖-[ [≡]-with(ext) (Morphism.identityᵣ(_∘_)(id)) ]
    ext(η(x))      🝖-[ ext-inverse ]
    id             🝖-end
  open Functor(functor)

  monad : Monad(T)
  Monad.functor monad = functor
  ∃.witness (Monad.Η monad) = η
  NaturalTransformation.natural (∃.proof (Monad.Η monad)) = symmetry(_≡_) ext-identity
  ∃.witness (Monad.Μ monad) = μ
  NaturalTransformation.natural (∃.proof (Monad.Μ monad)) {x} {y} {f} =
    μ(y) ∘ ext(η(T(y)) ∘ ext(η(y) ∘ f))      🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(y)) ∘ ext(η(y) ∘ f))   🝖-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(y)) ∘ ext(η(y) ∘ f))) 🝖-[ [≡]-with(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(y))) ∘ ext(η(y) ∘ f)) 🝖-[ [≡]-with(ext) ([≡]-with2ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ ext(η(y) ∘ f))                  🝖-[ [≡]-with(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(ext(η(y) ∘ f))                       🝖-[ [≡]-with(ext) (Morphism.identityᵣ(_∘_)(id)) ]-sym
    ext(ext(η(y) ∘ f) ∘ id)                  🝖-[ ext-distribute ]
    ext(η(y) ∘ f) ∘ ext(id)                  🝖[ _≡_ ]-[]
    ext(η(y) ∘ f) ∘ μ(x)                     🝖-end
  _⊜_.proof (Monad.μ-functor-[∘]-commutativity monad) {x} = -- TODO: Same as above?
    μ(x) ∘ map(μ(x))                   🝖[ _≡_ ]-[]
    ext(id) ∘ map(ext(id))             🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(x)) ∘ ext(id))   🝖-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(x)) ∘ ext(id))) 🝖-[ [≡]-with(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(x))) ∘ ext(id)) 🝖-[ [≡]-with(ext) ([≡]-with2ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ ext(id))                  🝖-[ [≡]-with(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(ext(id))                       🝖-[ [≡]-with(ext) (Morphism.identityᵣ(_∘_)(id)) ]-sym
    ext(ext(id) ∘ id)                  🝖-[ ext-distribute ]
    ext(id) ∘ ext(id)                  🝖[ _≡_ ]-[]
    μ(x) ∘ μ(T(x))                     🝖-end
  _⊜_.proof (Monad.μ-functor-[∘]-identityₗ monad) {x} =
    μ(x) ∘ ext(η(T(x)) ∘ η(x))      🝖[ _≡_ ]-[]
    ext(id) ∘ ext(η(T(x)) ∘ η(x))   🝖[ _≡_ ]-[ ext-distribute ]-sym
    ext(ext(id) ∘ (η(T(x)) ∘ η(x))) 🝖[ _≡_ ]-[ [≡]-with(ext) (symmetry(_≡_) (Morphism.associativity(_∘_))) ]
    ext((ext(id) ∘ η(T(x))) ∘ η(x)) 🝖[ _≡_ ]-[ [≡]-with(ext) ([≡]-with2ₗ(_∘_)(_) ext-identity) ]
    ext(id ∘ η(x))                  🝖[ _≡_ ]-[ [≡]-with(ext) (Morphism.identityₗ(_∘_)(id)) ]
    ext(η(x))                       🝖[ _≡_ ]-[ ext-inverse ]
    id                              🝖[ _≡_ ]-end
  _⊜_.proof (Monad.μ-functor-[∘]-identityᵣ monad) {x} =
    μ(x) ∘ η(T(x))    🝖[ _≡_ ]-[]
    ext(id) ∘ η(T(x)) 🝖[ _≡_ ]-[ ext-identity ]
    id                🝖[ _≡_ ]-end

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
