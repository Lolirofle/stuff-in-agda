import      Lvl

module Structure.Category.Category {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Structure.Category
open import Structure.Category.Functor.Equiv
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.Functor.Functors.Proofs

open CategoryObject
open Functors.Wrapped

categoryCategory : Category{Obj = CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (_→ᶠᵘⁿᶜᵗᵒʳ_)
Category._∘_            categoryCategory = _∘ᶠᵘⁿᶜᵗᵒʳ_
Category.id             categoryCategory = idᶠᵘⁿᶜᵗᵒʳ
Category.binaryOperator categoryCategory = [∘ᶠᵘⁿᶜᵗᵒʳ]-binaryOperator
Category.associativity  categoryCategory = [∘ᶠᵘⁿᶜᵗᵒʳ]-associativity
Category.identity       categoryCategory = [∘ᶠᵘⁿᶜᵗᵒʳ]-identity
