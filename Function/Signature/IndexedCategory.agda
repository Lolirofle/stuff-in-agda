module Function.Signature.IndexedCategory where

open import Function as Fn using (_→ᶠ_)
open import Functional.Implicit using (_﹛→﹜_)
open import Functional.Instance using (_⦃→⦄_)
import      Lvl
open import Signature.IndexedCategory
open import Signature.IndexedCategory.Functor
open import Type

-- The indexed category signature of a function type.
explicitFunction : IndexedCategory
explicitFunction = indexedCategory Lvl.Level (\ℓ → Type{ℓ}) (_→ᶠ_)

-- The indexed category signature of an implicit function type.
implicitFunction : IndexedCategory
implicitFunction = indexedCategory Lvl.Level (\ℓ → Type{ℓ}) (_﹛→﹜_)

-- The indexed category signature of an instance function type.
instanceFunction : IndexedCategory
instanceFunction = indexedCategory Lvl.Level (\ℓ → Type{ℓ}) (_⦃→⦄_)

HomFunctor : IndexedCategory → Typeω
HomFunctor C = Functor C explicitFunction

open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Typeω.Dependent.Sigma

module HomFunctor
  {C : IndexedCategory}
  ((intro F map) : C →ᶠᵘⁿᶜᵗᵒʳ explicitFunction)
  where

  open IndexedCategory(C)
  open Functor(F)

  module _
    {i₁ i₂}
    {A : Obj i₁}
    {B : Obj i₂}
    {ℓₑ} ⦃ equiv : Equiv{ℓₑ}(Functor.obj(F) B) ⦄
    where

    _⊜_ : (A ⟶ B) → (A ⟶ B) → Type
    f ⊜ g = ∀{x} → ((map f x) ≡ (map g x))

    instance
      [⊜]-reflexivity : Reflexivity(_⊜_)
      [⊜]-reflexivity = intro(Reflexivity.proof(Equiv.reflexivity equiv))

    instance
      [⊜]-symmetry : Symmetry(_⊜_)
      [⊜]-symmetry = intro(\p → Symmetry.proof(Equiv.symmetry equiv) p)

    instance
      [⊜]-transitivity : Transitivity(_⊜_)
      [⊜]-transitivity = intro(\p q → Transitivity.proof(Equiv.transitivity equiv) p q)

    instance
      Morphism-equiv : Equiv(A ⟶ B)
      Morphism-equiv = intro(_⊜_) ⦃ intro ⦄
