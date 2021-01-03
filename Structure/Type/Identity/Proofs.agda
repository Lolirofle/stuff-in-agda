module Structure.Type.Identity.Proofs where

import      Lvl
open import Functional using (_→ᶠ_ ; id ; _on₂_ ; swap ; _$_ ; apply)
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Proofs.Structures
open import Structure.Function
open import Structure.Setoid using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator
open import Structure.Type.Identity
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ ℓₘₑ ℓₚ ℓₒ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T
private variable Id _≡_ _▫_ : T → T → Stmt{ℓ}

module _ {_≡_ : Type{ℓ} → Type{ℓ} → Stmt{ℓₑ}} ⦃ minRefl : MinimalReflexiveRelation{ℓₚ = ℓ}(_≡_) ⦄ where
  minimal-reflection-coercion : ((_≡_) ⊆₂ (_→ᶠ_))
  minimal-reflection-coercion = minRefl{_→ᶠ_}

module _
  {_≡_ : A → A → Stmt{ℓₑ₁}} ⦃ minRefl : MinimalReflexiveRelation{ℓₚ = ℓₑ₂}(_≡_) ⦄
  {_▫_ : B → B → Stmt{ℓₑ₂}} ⦃ op-refl : Reflexivity(_▫_) ⦄
  {f : A → B}
  where

  minimal-reflection-transport : (_≡_) ⊆₂ ((_▫_) on₂ f)
  minimal-reflection-transport = intro (sub₂(_≡_)((_▫_) on₂ f) ⦃ minRefl ⦃ on₂-reflexivity ⦄ ⦄)

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ minRefl : MinimalReflexiveRelation{ℓₚ = ℓₑ₂}(Equiv._≡_ equiv-A) ⦄ where
  minimal-reflection-to-function : ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {f : A → B} → Function ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (f)
  minimal-reflection-to-function {f = f} = intro (sub₂(Equiv._≡_ equiv-A)((_≡ₛ_) on₂ f) ⦃ minimal-reflection-transport ⦄)

module _ ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ ⦃ minRefl : MinimalReflexiveRelation{ℓₚ = ℓ}(Equiv._≡_ equiv-T) ⦄ where
  minimal-reflection-to-relator : ∀{P : T → Stmt{ℓ}} → UnaryRelator(P)
  minimal-reflection-to-relator {P = P} = intro (sub₂(Equiv._≡_ equiv-T)((_→ᶠ_) on₂ P) ⦃ minimal-reflection-transport ⦄)

module _ ⦃ minRefl : MinimalReflexiveRelation(_≡_) ⦄ where
  minimal-reflection-to-flipped-transitivityᵣ : Names.FlippedTransitivityᵣ(_≡_)
  minimal-reflection-to-flipped-transitivityᵣ {z = z} = sub₂(_≡_)((_→ᶠ_) on₂ (_≡ z)) ⦃ minimal-reflection-transport ⦄

module _ ⦃ refl : Reflexivity(_≡_) ⦄ ⦃ minRefl : MinimalReflexiveRelation(_≡_) ⦄ where
  minimal-reflection-to-symmetry : Symmetry(_≡_)
  Symmetry.proof minimal-reflection-to-symmetry = sub₂(_≡_)(swap(_≡_)) ⦃ minRefl ⦃ swap-reflexivity ⦄ ⦄

  minimal-reflection-to-transitivity : Transitivity(_≡_)
  Transitivity.proof minimal-reflection-to-transitivity xy yz = minimal-reflection-to-flipped-transitivityᵣ (symmetry(_≡_) ⦃ minimal-reflection-to-symmetry ⦄ xy) yz

  minimal-reflection-to-equivalence : Equivalence(_≡_)
  Equivalence.reflexivity  minimal-reflection-to-equivalence = refl
  Equivalence.symmetry     minimal-reflection-to-equivalence = minimal-reflection-to-symmetry
  Equivalence.transitivity minimal-reflection-to-equivalence = minimal-reflection-to-transitivity

module _ ⦃ refl-Id : Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator{ℓₚ = ℓₚ}(Id) ⦄ where
  identity-eliminator-to-reflexive-subrelation : MinimalReflexiveRelation(Id)
  identity-eliminator-to-reflexive-subrelation {_▫_ = _▫_} = intro(idElim(Id) (\{x y} _ → (x ▫ y)) (reflexivity(_▫_)))

module _ ⦃ refl : Reflexivity(Id) ⦄ ⦃ identElim : IdentityEliminator(Id) ⦄ where
  identity-eliminator-to-symmetry : Symmetry(Id)
  identity-eliminator-to-symmetry = minimal-reflection-to-symmetry ⦃ minRefl = identity-eliminator-to-reflexive-subrelation ⦄

  identity-eliminator-to-flipped-transitivityᵣ : Names.FlippedTransitivityᵣ(Id)
  identity-eliminator-to-flipped-transitivityᵣ = minimal-reflection-to-flipped-transitivityᵣ ⦃ minRefl = identity-eliminator-to-reflexive-subrelation ⦄

  identity-eliminator-to-transitivity : Transitivity(Id)
  identity-eliminator-to-transitivity = minimal-reflection-to-transitivity ⦃ minRefl = identity-eliminator-to-reflexive-subrelation ⦄

  identity-eliminator-to-equivalence : Equivalence(Id)
  Equivalence.reflexivity  identity-eliminator-to-equivalence = refl
  Equivalence.symmetry     identity-eliminator-to-equivalence = identity-eliminator-to-symmetry
  Equivalence.transitivity identity-eliminator-to-equivalence = identity-eliminator-to-transitivity
