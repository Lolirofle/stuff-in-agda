-- This module just renames the proofs in Structure.Type.Identity.Eliminator.Equality.
module Structure.Type.Identity.Eliminator.Functions where

open import Functional
import      Lvl
open import Logic
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Type.Identity
open import Structure.Type.Identity.Eliminator.Equality
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑ ℓₚ : Lvl.Level
private variable T A B : Type{ℓ}

module Oper (Id : A → A → Type{ℓₑ}) ⦃ intro :  Reflexivity(Id) ⦄ ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄ where
  open Symmetry    (identityEliminator-to-symmetry     ⦃ intro ⦄ ⦃ elim ⦄) using () renaming (proof to sym)   public
  open Transitivity(identityEliminator-to-transitivity ⦃ intro ⦄ ⦃ elim ⦄) using () renaming (proof to trans) public
  flippedTransᵣ = identityEliminator-to-flippedTransitivityᵣ ⦃ intro ⦄ ⦃ elim ⦄
  comp : ∀{x y z} → Id y z → Id x y → Id x z
  comp = swap trans
  module _ (_▫_ : A → A → Type{ℓₚ}) ⦃ [▫]-refl : Reflexivity(_▫_) ⦄ where open _⊆₂_ (identityEliminator-to-reflexive-subrelation ⦃ intro ⦄ ⦃ elim{ℓₚ} ⦄) using () renaming (proof to sub) public
  module _ (f : A → B) ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where open Function ⦃ _ ⦄ (identityEliminator-to-function ⦃ refl = intro ⦄ ⦃ elim ⦄ {f = f}) using () renaming (congruence to congₑ) public
  module _ (f : A → A) where open Function ⦃ _ ⦄ ⦃ _ ⦄ (identityEliminator-to-function ⦃ refl = intro ⦄ ⦃ elim ⦄ ⦃ identityEliminator-to-equiv ⦄ {f = f}) using () renaming (congruence to cong) public
  open Reflexivity(intro) using () renaming (proof to refl)  public

module TypeOper (Id : Type → Type → Type{ℓₑ}) ⦃ intro :  Reflexivity(Id) ⦄ ⦃ elim : IdentityEliminator(Id) {ℓₚ} ⦄ where
  open _⊆₂_ (identityEliminator-to-coercion ⦃ refl = intro ⦄ ⦃ elim ⦄) using () renaming (proof to coerce) public

module Oper₂
  (Id₁ : A → A → Type{ℓₑ₁}) ⦃ intro₁ :  Reflexivity(Id₁) ⦄ ⦃ elim₁ : ∀{ℓₚ} → IdentityEliminator(Id₁) {ℓₚ} ⦄
  (Id₂ : B → B → Type{ℓₑ₂}) ⦃ intro₂ :  Reflexivity(Id₂) ⦄ ⦃ elim₂ : ∀{ℓₚ} → IdentityEliminator(Id₂) {ℓₚ} ⦄
  where

  module _ (f : A → B) where open Function ⦃ _ ⦄ ⦃ _ ⦄ (identityEliminator-to-function ⦃ refl = intro₁ ⦄ ⦃ elim₁ ⦄ ⦃ identityEliminator-to-equiv ⦄ {f = f}) using () renaming (congruence to cong) public
