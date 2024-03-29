module Relator.Equals.Proofs.Equivalence where

open import Functional
import      Lvl
open import Functional.Instance
open import Logic.Propositional
open import Logic
open import Relator.Equals
open import Structure.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Structure.Function
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Structure.Type.Identity.Proofs
open import Type

-- TODO: Consider using Structure.Type.Identity instead of these proofs

module One {ℓ} {T : Type{ℓ}} where
  import Type.Identity.Proofs
  open   Type.Identity.Proofs.One{T = T}
    using()
    renaming(
      Id-identityEliminator       to [≡]-identity-eliminator ;
      Id-reflexivity              to [≡]-reflexivity ;
      Id-symmetry                 to [≡]-symmetry ;
      Id-transitivity             to [≡]-transitivity ;
      Id-equivalence              to [≡]-equivalence ;
      Id-equiv                    to [≡]-equiv ;
      Id-minimalReflexiveRelation to [≡]-sub-of-reflexive
    ) public

  [≡]-to-equivalence : ∀{ℓₗ}{x y : T} → (x ≡ y) → ⦃ equiv-T : Equiv{ℓₗ}(T) ⦄ → (_≡ₛ_ ⦃ equiv-T ⦄ x y)
  [≡]-to-equivalence([≡]-intro) = reflexivity(_≡ₛ_)

  private -- TODO: Remove these
    -- Replaces occurrences of an element in a function
    [≡]-substitutionᵣ : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) → f(y)
    [≡]-substitutionᵣ [≡]-intro p = p -- TODO: Express in terms of sub-of-reflexive which is transport so that functors are automatically something

    -- Replaces occurrences of an element in a function
    [≡]-substitutionₗ : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(y) → f(x)
    [≡]-substitutionₗ [≡]-intro p = p

    [≡]-substitution : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → (f(x) ↔ f(y))
    [≡]-substitution eq = [↔]-intro ([≡]-substitutionₗ eq) ([≡]-substitutionᵣ eq)

  [≡]-unaryRelator : ∀{ℓ₂}{P : T → Stmt{ℓ₂}} → UnaryRelator ⦃ [≡]-equiv ⦄ (P)
  [≡]-unaryRelator{P = P} = intro(\xy → [≡]-substitution xy {f = P})
open One public

module Two {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} where
  private
    -- Applies a function to each side of the equality (TODO: Remove this and use Function everywhere instead)
    [≡]-with : (f : A → B) → ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
    [≡]-with f [≡]-intro = [≡]-intro

  [≡]-function : ∀{f} → Function ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (f)
  Function.congruence([≡]-function {f}) eq = [≡]-with(f) eq

  [≡]-to-function : ∀{ℓₗ} → ⦃ equiv-B : Equiv{ℓₗ}(B) ⦄ → ∀{f : A → B} → Function ⦃ [≡]-equiv ⦄ ⦃ equiv-B ⦄ (f)
  Function.congruence ([≡]-to-function) [≡]-intro = reflexivity(_≡ₛ_)

  [≡]-binaryRelator : ∀{ℓ}{P : A → B → Stmt{ℓ}} → BinaryRelator ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (P)
  BinaryRelator.substitution [≡]-binaryRelator [≡]-intro [≡]-intro = [↔]-intro id id
open Two public

module Three {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} {ℓ₃}{C : Type{ℓ₃}} where
  [≡]-binaryOperator : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(C) ⦄ {_▫_ : A → B → C} → BinaryOperator ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ ⦃ equiv ⦄ (_▫_)
  BinaryOperator.congruence [≡]-binaryOperator [≡]-intro [≡]-intro = reflexivity(_≡ₛ_)
open Three public

module Four {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} {ℓ₃}{C : Type{ℓ₃}} {ℓ₄}{D : Type{ℓ₄}} where
  [≡]-trinaryOperator : ∀{ℓₑ} ⦃ equiv : Equiv{ℓₑ}(D) ⦄ {_▫_▫_ : A → B → C → D} → TrinaryOperator ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ ⦃ equiv ⦄ (_▫_▫_)
  TrinaryOperator.congruence([≡]-trinaryOperator {_▫_▫_}) [≡]-intro [≡]-intro [≡]-intro = reflexivity(_≡ₛ_)
open Four public
