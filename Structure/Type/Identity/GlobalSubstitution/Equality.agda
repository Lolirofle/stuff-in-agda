module Structure.Type.Identity.GlobalSubstitution.Equality where

open import BidirectionalFunction using (_$ₗ_ ; _$ᵣ_)
open import Functional using (id ; _on₂_ ; swap ; _$_)
open import Logic
import      Lvl
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Structure.Type.Identity.MinimalReflexiveRelation.Equality
open import Type

private variable ℓ ℓₑ ℓₚ : Lvl.Level
private variable T : Type{ℓ}
private variable x y : T
private variable _≡_ : T → T → Stmt{ℓ}

module _ {_≡_ : Type{ℓ} → Type{ℓ} → Stmt{ℓₑ}} (subst : GlobalSubstitution{ℓₚ = ℓ}(_≡_)) where
  globalSubstitution-to-reflexivity : Reflexivity(_≡_)
  globalSubstitution-to-reflexivity = intro(subst $ₗ \_ → id)

  globalSubstitution-to-minimalReflexive : MinimalReflexiveRelation{ℓₚ = ℓ}(_≡_)
  globalSubstitution-to-minimalReflexive{_▫_ = _▫_} = intro \{x}{y} xy → (subst $ᵣ xy) (x ▫_) (reflexivity(_▫_))

module _ {_≡_ : Type{ℓ} → Type{ℓ} → Stmt{ℓ}} (subst : GlobalSubstitution{ℓₚ = ℓ}(_≡_)) where
  globalSubstitution-to-symmetry : Symmetry(_≡_)
  globalSubstitution-to-symmetry = minimal-reflection-to-symmetry ⦃ globalSubstitution-to-reflexivity subst ⦄ ⦃ globalSubstitution-to-minimalReflexive subst ⦄
  
  globalSubstitution-to-transitivity : Transitivity(_≡_)
  globalSubstitution-to-transitivity = minimal-reflection-to-transitivity ⦃ globalSubstitution-to-reflexivity subst ⦄ ⦃ globalSubstitution-to-minimalReflexive subst ⦄
