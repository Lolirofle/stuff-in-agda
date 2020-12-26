module Structure.Category.NaturalTransformation.Equiv where

import      Function.Equals
open        Function.Equals.Dependent
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Setoid
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type


module _
  {ℓₗₒ ℓₗₘ ℓₗₑ ℓᵣₒ ℓᵣₘ ℓᵣₑ}
  {catₗ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ}}
  {catᵣ : CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ}}
  {F₁ : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ}
  {F₂ : catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ}
  where

  _≡ᴺᵀ_ : (F₁ →ᴺᵀ F₂) → (F₁ →ᴺᵀ F₂) → Stmt
  [∃]-intro N₁ ≡ᴺᵀ [∃]-intro N₂ = N₁ ⊜ N₂

  instance
    [≡ᴺᵀ]-reflexivity : Reflexivity(_≡ᴺᵀ_)
    Reflexivity.proof [≡ᴺᵀ]-reflexivity = reflexivity(_⊜_)

  instance
    [≡ᴺᵀ]-symmetry : Symmetry(_≡ᴺᵀ_)
    Symmetry.proof [≡ᴺᵀ]-symmetry = symmetry(_⊜_)

  instance
    [≡ᴺᵀ]-transitivity : Transitivity(_≡ᴺᵀ_)
    Transitivity.proof [≡ᴺᵀ]-transitivity = transitivity(_⊜_)

  instance
    [≡ᴺᵀ]-equivalence : Equivalence(_≡ᴺᵀ_)
    [≡ᴺᵀ]-equivalence = intro

  instance
    [→ᴺᵀ]-equiv : Equiv(F₁ →ᴺᵀ F₂)
    [→ᴺᵀ]-equiv = intro(_≡ᴺᵀ_) ⦃ [≡ᴺᵀ]-equivalence ⦄
