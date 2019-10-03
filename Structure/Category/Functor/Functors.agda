module Structure.Category.Functor.Functors where

open import Functional
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Operator.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

open Functor

module _
  {ℓₒₗ ℓₘₗ ℓₒᵣ ℓₘᵣ : Lvl.Level}
  {Objₗ : Set(ℓₒₗ)}
  {Objᵣ : Set(ℓₒᵣ)}
  {Morphismₗ : Objₗ → Objₗ → Set(ℓₘₗ)}
  ⦃ morphism-equivₗ : ∀{x y} → Equiv(Morphismₗ x y) ⦄
  {Morphismᵣ : Objᵣ → Objᵣ → Set(ℓₘᵣ)}
  ⦃ morphism-equivᵣ : ∀{x y} → Equiv(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  module _ where

    open module Equivₗ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivₗ{x}{y} ⦄) using () renaming (transitivity to transitivityₗ ; symmetry to symmetryₗ ; reflexivity to reflexivityₗ)
    open module Equivᵣ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivᵣ{x}{y} ⦄) using () renaming (transitivity to transitivityᵣ ; symmetry to symmetryᵣ ; reflexivity to reflexivityᵣ)
    open SideNotation(Categoryₗ)(Categoryᵣ)
    open Functor

    -- A constant functor maps every object and morphism in a category to a single specified object and the identity morphism.
    constantFunctor : (objᵣ : Objᵣ) → Functor(Categoryₗ)(Categoryᵣ)(const(objᵣ))
    map           (constantFunctor(objᵣ)) = const(idᵣ)
    op-preserving (constantFunctor(objᵣ)) = symmetry(_≡_) (identityₗ(_∘ᵣ_)(idᵣ))
    id-preserving (constantFunctor(objᵣ)) = reflexivity(_≡_)

module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Set(ℓₒ)}
  {Morphism : Obj → Obj → Set(ℓₘ)}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  {Category : Category(Morphism)}
  where

  open import Functional
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  open module [≡]-Equivalence {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv{x}{y} ⦄) using () renaming (transitivity to [≡]-transitivity ; symmetry to [≡]-symmetry ; reflexivity to [≡]-reflexivity)
  open Functor

  identityFunctor : Endofunctor(Category)(id)
  map           (identityFunctor) = id
  op-preserving(identityFunctor)  = reflexivity(_≡_)
  id-preserving (identityFunctor) = reflexivity(_≡_)

module _
  {ℓₒ₁ ℓₘ₁ ℓₒ₂ ℓₘ₂ ℓₒ₃ ℓₘ₃ : Lvl.Level}
  {Obj₁ : Set(ℓₒ₁)}
  {Obj₂ : Set(ℓₒ₂)}
  {Obj₃ : Set(ℓₒ₃)}
  {Morphism₁ : Obj₁ → Obj₁ → Set(ℓₘ₁)}
  {Morphism₂ : Obj₂ → Obj₂ → Set(ℓₘ₂)}
  {Morphism₃ : Obj₃ → Obj₃ → Set(ℓₘ₃)}
  ⦃ morphism-equiv₁ : ∀{x y} → Equiv(Morphism₁ x y) ⦄
  ⦃ morphism-equiv₂ : ∀{x y} → Equiv(Morphism₂ x y) ⦄
  ⦃ morphism-equiv₃ : ∀{x y} → Equiv(Morphism₃ x y) ⦄
  {Category₁ : Category(Morphism₁)}
  {Category₂ : Category(Morphism₂)}
  {Category₃ : Category(Morphism₃)}
  where

  open import Functional
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties

  -- open module Equiv₁ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv₁{x}{y} ⦄) using () renaming (transitivity to transitivity₁ ; symmetry to symmetry₁ ; reflexivity to reflexivity₁)
  -- open module Equiv₂ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv₂{x}{y} ⦄) using () renaming (transitivity to transitivity₂ ; symmetry to symmetry₂ ; reflexivity to reflexivity₂)
  open module Equiv₃ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv₃{x}{y} ⦄) using () renaming (transitivity to transitivity₃ ; symmetry to symmetry₃ ; reflexivity to reflexivity₃)
  open Functor

  compositionFunctor :
    ∀{F₂₃}{F₁₂}
    → (functor₂₃ : Functor(Category₂)(Category₃)(F₂₃))
    → ⦃ _ : ∀{x y} → Function(map(functor₂₃) {x}{y}) ⦄
    → (functor₁₂ : Functor(Category₁)(Category₂)(F₁₂))
    → ⦃ _ : ∀{x y} → Function(map(functor₁₂) {x}{y}) ⦄
    → Functor(Category₁)(Category₃)(F₂₃ ∘ F₁₂)

  map           (compositionFunctor{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)){x}{y} = (map(functor₂₃){F₁₂(x)}{F₁₂(y)}) ∘ (map(functor₁₂){x}{y})
  op-preserving (compositionFunctor{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)){x}{y}{z} {f}{g} =
    transitivity(_≡_) ⦃ transitivity₃ ⦄
      ([≡]-with(map(functor₂₃)) (op-preserving(functor₁₂) {x}{y}{z} {f}{g}))
      (op-preserving(functor₂₃) {F₁₂(x)} {F₁₂(y)} {F₁₂(z)} {map(functor₁₂)(f)} {map(functor₁₂)(g)})

  id-preserving (compositionFunctor{F₂₃}{F₁₂}(functor₂₃)(functor₁₂)) {x} =
    transitivity(_≡_) ⦃ transitivity₃ ⦄
      ([≡]-with(map(functor₂₃)) (id-preserving(functor₁₂) {x}))
      (id-preserving(functor₂₃) {F₁₂(x)})
    -- map₁₂(id₁{x}) ≡ id₂{F₁₂(x)}
    -- map₂₃(map₁₂(id₁{x})) ≡ map₂₃(id₂{F₁₂(x)})
    --                      ≡ id₃{F₂₃(F₁₂(x))}
    -- (map₂₃ ∘ map₁₂)(id₁{x}) ≡ id₃{F₂₃(F₁₂(x))}
