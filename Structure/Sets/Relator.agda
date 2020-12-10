module Structure.Sets.Relator where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Structure.Sets.Names as Names
open import Type

private variable ℓ ℓₗ ℓᵣ ℓᵣₑₗ : Lvl.Level
private variable S Sₗ Sᵣ E Eₗ Eᵣ : Type{ℓ}
private variable _∈ₗ_ : E → Sₗ → Stmt{ℓₗ}
private variable _∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}

module _ (_∈ₗ_ : E → Sₗ → Stmt{ℓₗ}) (_∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}) where
  record SetEqualityRelation (_≡_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ}) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓᵣₑₗ} where
    constructor intro
    field membership : Names.SetEqualityMembership(_∈ₗ_)(_∈ᵣ_)(_≡_)

  record SubsetRelation (_⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣₑₗ}) : Type{Lvl.of(E) Lvl.⊔ Lvl.of(Sₗ) Lvl.⊔ Lvl.of(Sᵣ) Lvl.⊔ ℓₗ Lvl.⊔ ℓᵣ Lvl.⊔ ℓᵣₑₗ} where
    constructor intro
    field membership : Names.SubsetMembership(_∈ₗ_)(_∈ᵣ_)(_⊆_)

module _ ⦃ eq : ∃(SetEqualityRelation(_∈ₗ_)(_∈ᵣ_){ℓᵣₑₗ}) ⦄ where
  open ∃(eq) using () renaming (witness to _≡_) public
  open SetEqualityRelation([∃]-proof eq) using () renaming (membership to [≡]-membership) public

  _≢_ = (¬_) ∘₂ (_≡_)

module _ ⦃ subset : ∃(SubsetRelation(_∈ₗ_)(_∈ᵣ_){ℓᵣ}) ⦄ where
  open ∃(subset) using () renaming (witness to _⊆_) public
  open SubsetRelation([∃]-proof subset) using () renaming (membership to [⊆]-membership) public
  open Names.From-[⊆] (_⊆_) public
