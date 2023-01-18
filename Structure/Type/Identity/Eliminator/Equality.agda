module Structure.Type.Identity.Eliminator.Equality where

open import Function using (_→ᶠ_)
import      Lvl
open import Logic
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid
open import Structure.Type.Identity
open import Structure.Type.Identity.MinimalReflexiveRelation.Equality
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ ℓₘₑ ℓₚ ℓₒ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x y z : T
private variable Id Id₁ Id₂ : T → T → Stmt{ℓ}

module _ ⦃ refl : Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator(Id) {ℓₚ} ⦄ where
  identityEliminator-to-reflexive-subrelation : MinimalReflexiveRelation(Id)
  identityEliminator-to-reflexive-subrelation {_▫_ = _▫_} = intro(idElim(Id) (\{x y} _ → (x ▫ y)) (reflexivity(_▫_)))

module _ ⦃ refl : Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator(Id) ⦄ where
  identityEliminator-to-symmetry : Symmetry(Id)
  identityEliminator-to-symmetry = minimal-reflection-to-symmetry ⦃ minRefl = identityEliminator-to-reflexive-subrelation ⦄

  identityEliminator-to-flippedTransitivityᵣ : Names.FlippedTransitivityᵣ(Id)
  identityEliminator-to-flippedTransitivityᵣ = minimal-reflection-to-flipped-transitivityᵣ ⦃ minRefl = identityEliminator-to-reflexive-subrelation ⦄

  identityEliminator-to-transitivity : Transitivity(Id)
  identityEliminator-to-transitivity = minimal-reflection-to-transitivity ⦃ minRefl = identityEliminator-to-reflexive-subrelation ⦄

  identityEliminator-to-equivalence : Equivalence(Id)
  Equivalence.reflexivity  identityEliminator-to-equivalence = refl
  Equivalence.symmetry     identityEliminator-to-equivalence = identityEliminator-to-symmetry
  Equivalence.transitivity identityEliminator-to-equivalence = identityEliminator-to-transitivity

  identityEliminator-to-equiv : Equiv(Function.domain(Id))
  identityEliminator-to-equiv = intro(Id) ⦃ identityEliminator-to-equivalence ⦄

module _ ⦃ refl : Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator{T = Type}(Id) ⦄ where
  identityEliminator-to-coercion : (Id ⊆₂ (_→ᶠ_))
  identityEliminator-to-coercion = minimal-reflection-coercion ⦃ identityEliminator-to-reflexive-subrelation ⦄

module _ ⦃ refl : Reflexivity{T = A}(Id) ⦄ ⦃ identElim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  identityEliminator-to-function : ∀{f : A → B} → Function ⦃ identityEliminator-to-equiv ⦄ f
  identityEliminator-to-function = minimal-reflection-to-function ⦃ _ ⦄ ⦃ minRefl-A = identityEliminator-to-reflexive-subrelation ⦄

module _
  ⦃ refl-A : Reflexivity{T = A}(Id₁) ⦄ ⦃ identElim-A : ∀{ℓₚ} → IdentityEliminator(Id₁) {ℓₚ} ⦄
  ⦃ refl-B : Reflexivity{T = B}(Id₂) ⦄ ⦃ identElim-B : ∀{ℓₚ} → IdentityEliminator(Id₂) {ℓₚ} ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  where

  identityEliminator-to-binaryOperator : ∀{f : A → B → C} → BinaryOperator ⦃ identityEliminator-to-equiv ⦄ ⦃ identityEliminator-to-equiv ⦄ f
  identityEliminator-to-binaryOperator = minimal-reflection-to-binaryOperator
    ⦃ _ ⦄ ⦃ minRefl-A = identityEliminator-to-reflexive-subrelation ⦄
    ⦃ _ ⦄ ⦃ minRefl-B = identityEliminator-to-reflexive-subrelation ⦄
