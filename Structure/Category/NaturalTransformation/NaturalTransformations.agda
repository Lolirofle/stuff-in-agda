import      Lvl
open import Sets.Setoid
open import Type

module Structure.Category.NaturalTransformation.NaturalTransformations
  {ℓₒₗ ℓₒᵣ ℓₘₗ ℓₘᵣ : Lvl.Level}
  {Objₗ : Type{ℓₒₗ}}
  {Objᵣ : Type{ℓₒᵣ}}
  {Morphismₗ : Objₗ → Objₗ → Type{ℓₘₗ}}
  {Morphismᵣ : Objᵣ → Objᵣ → Type{ℓₘᵣ}}
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv(Morphismᵣ x y) ⦄
  where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
open import Logic
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Category.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Syntax.Transitivity

private variable F F₁ F₂ F₃ : Objₗ → Objᵣ

module Raw
  (catₗ : Category(Morphismₗ))
  (catᵣ : Category(Morphismᵣ))
  where

  private instance _ = catₗ
  private instance _ = catᵣ

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄ hiding (identity)

  idᴺᵀ : (x : Objₗ) → (F(x) ⟶ F(x))
  idᴺᵀ _ = id

  _∘ᴺᵀ_ : ((x : Objₗ) → (F₂(x) ⟶ F₃(x))) → ((x : Objₗ) → (F₁(x) ⟶ F₂(x))) → ((x : Objₗ) → (F₁(x) ⟶ F₃(x)))
  (comp₁ ∘ᴺᵀ comp₂)(x) = comp₁(x) ∘ comp₂(x)

module _
  {catₗ : Category(Morphismₗ)}
  {catᵣ : Category(Morphismᵣ)}
  where

  private instance _ = catₗ
  private instance _ = catᵣ

  open Category ⦃ … ⦄ hiding (identity)
  open Functor ⦃ … ⦄
  private open module Equivᵣ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivᵣ{x}{y} ⦄) using ()

  module _ where
    open Raw(catₗ)(catᵣ)

    module _ {functor@([∃]-intro F) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      identity : NaturalTransformation(functor)(functor)(idᴺᵀ)
      NaturalTransformation.natural identity {x} {y} {f} =
        id ∘ map f 🝖-[ Morphism.identityₗ(_)(id) ⦃ Category.identityₗ(catᵣ) ⦄ ]
        map f      🝖-[ Morphism.identityᵣ(_)(id) ⦃ Category.identityᵣ(catᵣ) ⦄ ]-sym
        map f ∘ id 🝖-end

    module _ {functor₁@([∃]-intro F₁) functor₂@([∃]-intro F₂) functor₃@([∃]-intro F₃) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      composition : ∀{comp₁ comp₂} → NaturalTransformation(functor₂)(functor₃)(comp₁) → NaturalTransformation(functor₁)(functor₂)(comp₂) → NaturalTransformation(functor₁)(functor₃)(comp₁ ∘ᴺᵀ comp₂)
      NaturalTransformation.natural (composition {comp₁} {comp₂} nat₁ nat₂) {x} {y} {f} =
        (comp₁(y) ∘ comp₂(y)) ∘ map f 🝖-[ Morphism.associativity(_) ⦃ Category.associativity(catᵣ) ⦄ ]
        comp₁(y) ∘ (comp₂(y) ∘ map f) 🝖-[ [≡]-with2ᵣ(_∘_)(comp₁(y)) (NaturalTransformation.natural nat₂) ]
        comp₁(y) ∘ (map f ∘ comp₂(x)) 🝖-[ Morphism.associativity(_) ⦃ Category.associativity(catᵣ) ⦄ ]-sym
        (comp₁(y) ∘ map f) ∘ comp₂(x) 🝖-[ [≡]-with2ₗ(_∘_)(comp₂(x)) (NaturalTransformation.natural nat₁) ]
        (map f ∘ comp₁(x)) ∘ comp₂(x) 🝖-[ Morphism.associativity(_) ⦃ Category.associativity(catᵣ) ⦄ ]
        map f ∘ (comp₁(x) ∘ comp₂(x)) 🝖-end

  module Wrapped where
    module _ {functor@([∃]-intro F) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      idᴺᵀ : (F →ᴺᵀ F)
      idᴺᵀ = [∃]-intro (Raw.idᴺᵀ(catₗ)(catᵣ)) ⦃ identity ⦄

    module _ {functor₁@([∃]-intro F₁) functor₂@([∃]-intro F₂) functor₃@([∃]-intro F₃) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      _∘ᴺᵀ_ : (F₂ →ᴺᵀ F₃) → (F₁ →ᴺᵀ F₂) → (F₁ →ᴺᵀ F₃)
      _∘ᴺᵀ_ ([∃]-intro F ⦃ F-proof ⦄) ([∃]-intro G ⦃ G-proof ⦄) = [∃]-intro (Raw._∘ᴺᵀ_ (catₗ)(catᵣ) F G) ⦃ composition F-proof G-proof ⦄
