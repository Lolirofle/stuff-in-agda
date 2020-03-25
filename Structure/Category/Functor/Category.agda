module Structure.Category.Functor.Category where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
import      Lvl
open import Logic
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Type

functorCategory : ∀{catₗ catᵣ} → Category{Obj = catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ} (\x y → ∃(NaturalTransformation x y))
{-
_∘_           (functorCategory) = compositionNaturalTransformation
id            (functorCategory) = identityNaturalTransformation
identityₗ     (functorCategory) {F}{G} {N} rewrite identityₗ (Category₂) {_}{_} {id₂} = [≡]-intro
  -- For x: Functor(Category₁) (Category₂) , y: Functor(Category₁) (Category₂) , f: NaturalTransformation(x)(y)
  --
  -- identityNaturalTransformation ∘ f
  -- ≡ x ↦ component(identityNaturalTransformation)(x) ∘₂ component(f)(x)
  -- ≡ x ↦ id₂ ∘₂ component(f)(x)
  -- ≡ x ↦ component(f)(x)
  -- ≡ f
identityᵣ     (functorCategory) = [≡]-intro
associativity (functorCategory) = [≡]-intro
-}
