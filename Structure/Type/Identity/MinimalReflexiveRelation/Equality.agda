module Structure.Type.Identity.MinimalReflexiveRelation.Equality where

open import BidirectionalFunction
open import Function using (_→ᶠ_)
open import Functional using (id ; _on₂_ ; swap ; _$_ ; apply)
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Proofs.Structures
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator
open import Structure.Type.Identity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ ℓₘₑ ℓₚ ℓₒ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable x y : T
private variable Id _≡_ _≡₁_ _≡₂_ _▫_ : T → T → Stmt{ℓ}

module _ {_≡_ : Type{ℓ} → Type{ℓ} → Stmt{ℓₑ}} ⦃ minRefl : MinimalReflexiveRelation{ℓₚ = ℓ}(_≡_) ⦄ where
  minimal-reflection-coercion : ((_≡_) ⊆₂ (_→ᶠ_))
  minimal-reflection-coercion = minRefl{_→ᶠ_}

module _ ⦃ minRefl : MinimalReflexiveRelation(_≡_) ⦄ where
  minimal-reflection-to-flipped-transitivityᵣ : Names.FlippedTransitivityᵣ(_≡_)
  minimal-reflection-to-flipped-transitivityᵣ {z = z} = sub₂(_≡_)((_→ᶠ_) on₂ (_≡ z)) ⦃ minRefl ⦃ on₂-reflexivity ⦄ ⦄

module _ ⦃ refl : Reflexivity(_≡_) ⦄ ⦃ minRefl : MinimalReflexiveRelation(_≡_) ⦄ where
  minimal-reflection-to-symmetry : Symmetry(_≡_)
  Symmetry.proof minimal-reflection-to-symmetry = sub₂(_≡_)(swap(_≡_)) ⦃ minRefl ⦃ swap-reflexivity ⦄ ⦄

  minimal-reflection-to-transitivity : Transitivity(_≡_)
  Transitivity.proof minimal-reflection-to-transitivity {z = z} = sub₂(_≡_)((_←_) on₂ (_≡ z)) ⦃ minRefl ⦃ on₂-reflexivity ⦃ swap-reflexivity ⦄ ⦄ ⦄

  minimal-reflection-to-equivalence : Equivalence(_≡_)
  Equivalence.reflexivity  minimal-reflection-to-equivalence = refl
  Equivalence.symmetry     minimal-reflection-to-equivalence = minimal-reflection-to-symmetry
  Equivalence.transitivity minimal-reflection-to-equivalence = minimal-reflection-to-transitivity

  minimal-reflection-to-equiv : Equiv(_)
  minimal-reflection-to-equiv = intro(_≡_) ⦃ minimal-reflection-to-equivalence ⦄

module _
  ⦃ refl-A : Reflexivity(_≡_) ⦄ ⦃ minRefl-A : ∀{ℓₚ} → MinimalReflexiveRelation{ℓₚ = ℓₚ}{T = A}(_≡_) ⦄
  ⦃ equiv-B : Equiv{ℓₑ}(B) ⦄
  where

  minimal-reflection-to-function : ∀{f : A → B} → Function ⦃ minimal-reflection-to-equiv ⦄ (f)
  minimal-reflection-to-function {f = f} = intro(sub₂(_≡_)((_≡ₛ_) on₂ f) ⦃ minRefl-A ⦃ on₂-reflexivity ⦄ ⦄)

module _
  ⦃ refl-A : Reflexivity(_≡₁_) ⦄ ⦃ minRefl-A : ∀{ℓₚ} → MinimalReflexiveRelation{ℓₚ = ℓₚ}{T = A}(_≡₁_) ⦄
  ⦃ refl-B : Reflexivity(_≡₂_) ⦄ ⦃ minRefl-B : ∀{ℓₚ} → MinimalReflexiveRelation{ℓₚ = ℓₚ}{T = B}(_≡₂_) ⦄
  ⦃ equiv-C : Equiv{ℓₑ}(C) ⦄
  where

  minimal-reflection-to-binaryOperator : ∀{f : A → B → C} → BinaryOperator ⦃ minimal-reflection-to-equiv ⦄ ⦃ minimal-reflection-to-equiv ⦄ (f)
  minimal-reflection-to-binaryOperator {f = f} = BinaryOperator-unary-intro ⦃ _ ⦄ ⦃ _ ⦄ f minimal-reflection-to-function minimal-reflection-to-function

module _ ⦃ refl : Reflexivity(_≡_) ⦄ ⦃ minRefl : MinimalReflexiveRelation(_≡_) ⦄ where
  minimal-reflection-to-global-substitution : GlobalSubstitution(_≡_)
  minimal-reflection-to-global-substitution {x}{y} = intro
    (\subst → subst(x ≡_) (reflexivity(_≡_)))
    (\xy P → sub₂(_≡_)((_→ᶠ_) on₂ P) ⦃ minRefl ⦃ on₂-reflexivity ⦄ ⦄ xy)
