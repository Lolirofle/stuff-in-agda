module Structure.Category.NaturalTransformation.NaturalTransformations where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
open import Logic
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

open CategoryObject
private variable ℓₒₗ ℓₒᵣ ℓₘₗ ℓₘᵣ ℓₑₗ ℓₑᵣ : Lvl.Level

module Raw
  (catₗ : CategoryObject{ℓₒₗ}{ℓₘₗ}{ℓₑₗ})
  (catᵣ : CategoryObject{ℓₒᵣ}{ℓₘᵣ}{ℓₑᵣ})
  where

  private variable F F₁ F₂ F₃ : Object(catₗ) → Object(catᵣ)
  private instance _ = category catₗ
  private instance _ = category catᵣ

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄ hiding (identity)

  idᴺᵀ : (x : Object(catₗ)) → (F(x) ⟶ F(x))
  idᴺᵀ _ = id

  _∘ᴺᵀ_ : ((x : Object(catₗ)) → (F₂(x) ⟶ F₃(x))) → ((x : Object(catₗ)) → (F₁(x) ⟶ F₂(x))) → ((x : Object(catₗ)) → (F₁(x) ⟶ F₃(x)))
  (comp₁ ∘ᴺᵀ comp₂)(x) = comp₁(x) ∘ comp₂(x)

module _
  {catₗ : CategoryObject{ℓₒₗ}{ℓₘₗ}{ℓₑₗ}}
  {catᵣ : CategoryObject{ℓₒᵣ}{ℓₘᵣ}{ℓₑᵣ}}
  where

  private instance _ = category catₗ
  private instance _ = category catᵣ

  open Category ⦃ … ⦄ hiding (identity)
  open Functor ⦃ … ⦄
  private open module Equivᵣ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv(catᵣ){x}{y} ⦄) using ()

  module _ where
    open Raw(catₗ)(catᵣ)

    module _ {functor@([∃]-intro F) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      identity : NaturalTransformation(functor)(functor)(idᴺᵀ)
      NaturalTransformation.natural identity {x} {y} {f} =
        id ∘ map f 🝖-[ Morphism.identityₗ(_)(id) ⦃ identityₗ ⦄ ]
        map f      🝖-[ Morphism.identityᵣ(_)(id) ⦃ identityᵣ ⦄ ]-sym
        map f ∘ id 🝖-end

    module _ {functor₁@([∃]-intro F₁) functor₂@([∃]-intro F₂) functor₃@([∃]-intro F₃) : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} where
      composition : ∀{comp₁ comp₂} → NaturalTransformation(functor₂)(functor₃)(comp₁) → NaturalTransformation(functor₁)(functor₂)(comp₂) → NaturalTransformation(functor₁)(functor₃)(comp₁ ∘ᴺᵀ comp₂)
      NaturalTransformation.natural (composition {comp₁} {comp₂} nat₁ nat₂) {x} {y} {f} =
        (comp₁(y) ∘ comp₂(y)) ∘ map f 🝖-[ Morphism.associativity(_) ⦃ associativity ⦄ ]
        comp₁(y) ∘ (comp₂(y) ∘ map f) 🝖-[ congruence₂-₂(_∘_)(comp₁(y)) (NaturalTransformation.natural nat₂) ]
        comp₁(y) ∘ (map f ∘ comp₂(x)) 🝖-[ Morphism.associativity(_) ⦃ associativity ⦄ ]-sym
        (comp₁(y) ∘ map f) ∘ comp₂(x) 🝖-[ congruence₂-₁(_∘_)(comp₂(x)) (NaturalTransformation.natural nat₁) ]
        (map f ∘ comp₁(x)) ∘ comp₂(x) 🝖-[ Morphism.associativity(_) ⦃ associativity ⦄ ]
        map f ∘ (comp₁(x) ∘ comp₂(x)) 🝖-end

  module Wrapped where
    private variable F F₁ F₂ F₃ : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ

    idᴺᵀ : (F →ᴺᵀ F)
    idᴺᵀ = [∃]-intro (Raw.idᴺᵀ(catₗ)(catᵣ)) ⦃ identity ⦄

    _∘ᴺᵀ_ : (F₂ →ᴺᵀ F₃) → (F₁ →ᴺᵀ F₂) → (F₁ →ᴺᵀ F₃)
    _∘ᴺᵀ_ ([∃]-intro F ⦃ F-proof ⦄) ([∃]-intro G ⦃ G-proof ⦄) = [∃]-intro (Raw._∘ᴺᵀ_ (catₗ)(catᵣ) F G) ⦃ composition F-proof G-proof ⦄
