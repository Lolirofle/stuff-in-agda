module Structure.Set.Relations.Listable where

open import Data.List
import      Data.List.Relation.Membership as List
import      Data.List.Relation.Quantification as List
import      Lvl
open import Structure.Set
open import Structure.Setoid
open import Type

private variable ℓ ℓₗ ℓₑ ℓₑₑ ℓₑₛ : Lvl.Level
private variable S E : Type{ℓ}

module _
  ⦃ equiv-E : Equiv{ℓₑₑ}(E) ⦄
  ⦃ equiv-S : Equiv{ℓₑₛ}(S) ⦄
  {_∈_ : E → S → Type{ℓₗ}} ⦃ set-ext : SetExtensionality(_∈_) ⦄
  where

  record Listable(set : S) : Type{Lvl.of(E) Lvl.⊔ ℓₗ Lvl.⊔ ℓₑₑ} where
    field
      list : List(E)
    field
      correct  : List.AllElements(_∈ set) list
      complete : ∀{x} → (x ∈ set) → (x List.∈ list)
