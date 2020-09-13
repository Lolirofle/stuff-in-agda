module Relator.Equals.Proofs.Equivalence where

open import Functional
import      Lvl
open import Lang.Instance
open import Logic.Propositional
open import Logic
open import Relator.Equals
open import Structure.Setoid.WithLvl using (Equiv) renaming (_≡_ to _≡ₛ_)
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
  instance
    [≡]-reflexivity : Reflexivity (_≡_ {T = T})
    [≡]-reflexivity = intro [≡]-intro

  instance
    [≡]-identity-eliminator : ∀{ℓₚ} → IdentityEliminator{ℓₚ = ℓₚ}(_≡_ {T = T})
    IdentityEliminator.proof [≡]-identity-eliminator _ proof {x = x}{y = .x} [≡]-intro = proof{x}

  instance
    [≡]-symmetry : Symmetry (_≡_ {T = T})
    [≡]-symmetry = identity-eliminator-to-symmetry

  instance
    [≡]-transitivity : Transitivity (_≡_ {T = T})
    [≡]-transitivity = identity-eliminator-to-transitivity

  instance
    [≡]-equivalence : Equivalence (_≡_ {T = T})
    [≡]-equivalence = intro

  [≡]-to-equivalence : ∀{ℓₗ}{x y : T} → (x ≡ y) → ⦃ equiv-T : Equiv{ℓₗ}(T) ⦄ → (_≡ₛ_ ⦃ equiv-T ⦄ x y)
  [≡]-to-equivalence([≡]-intro) = reflexivity(_≡ₛ_)

  [≡]-equiv : Equiv{ℓ}(T)
  Equiv._≡_ [≡]-equiv = _≡_
  Equiv.equivalence [≡]-equiv = [≡]-equivalence

  -- Equality is a subrelation to every reflexive relation.
  -- One interpretation of this is that identity is the smallest reflexive relation when a relation is interpreted as a set of tuples and size is the cardinality of the set.
  instance
    [≡]-sub-of-reflexive : ∀{ℓₗ}{_▫_ : T → T → Stmt{ℓₗ}} → ⦃ _ : Reflexivity(_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))
    _⊆₂_.proof [≡]-sub-of-reflexive [≡]-intro = reflexivity(_)

  -- Replaces occurrences of an element in a function
  [≡]-substitutionᵣ : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) → f(y)
  [≡]-substitutionᵣ [≡]-intro p = p -- TODO: Express in terms of sub-of-reflexive which is transport so that functors are automatically something

  -- Replaces occurrences of an element in a function
  [≡]-substitutionₗ : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(y) → f(x)
  [≡]-substitutionₗ [≡]-intro p = p

  [≡]-substitution : ∀{ℓ₂}{x y} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → (f(x) ↔ f(y))
  [≡]-substitution eq = [↔]-intro ([≡]-substitutionₗ eq) ([≡]-substitutionᵣ eq)

  [≡]-unary-relator : ∀{ℓ₂}{P : T → Stmt{ℓ₂}} → UnaryRelator ⦃ [≡]-equiv ⦄ (P)
  UnaryRelator.substitution([≡]-unary-relator {P = P}) xy = [≡]-substitutionᵣ xy {P}
open One public

module Two {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} where
  -- Applies a function to each side of the equality (TODO: Remove this and use Function everywhere instead)
  [≡]-with : (f : A → B) → ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f [≡]-intro = [≡]-intro

  [≡]-function : ∀{f} → Function ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (f)
  Function.congruence([≡]-function {f}) eq = [≡]-with(f) eq

  [≡]-to-function : ∀{ℓₗ} → ⦃ equiv-B : Equiv{ℓₗ}(B) ⦄ → ∀{f : A → B} → Function ⦃ [≡]-equiv ⦄ ⦃ equiv-B ⦄ (f)
  Function.congruence ([≡]-to-function) [≡]-intro = reflexivity(_≡ₛ_)
open Two public

module Three {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} {ℓ₃}{C : Type{ℓ₃}} where
  -- Applies an operation to each side of the equality (TODO: Make this an instance of BinaryOperator instead)
  [≡]-with-op : (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
  [≡]-with-op (_▫_) [≡]-intro [≡]-intro = [≡]-intro
  -- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
  --   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with(x ↦ (x ▫ b₁)) (a₁≡a₂))

  [≡]-binary-operator : ∀{_▫_} → BinaryOperator ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄ (_▫_)
  BinaryOperator.congruence([≡]-binary-operator {_▫_}) aeq beq = [≡]-with-op(_▫_) aeq beq
open Three public
