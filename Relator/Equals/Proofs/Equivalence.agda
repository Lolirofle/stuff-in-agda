module Relator.Equals.Proofs.Equivalence where

import      Lvl
open import Lang.Instance
open import Logic
open import Relator.Equals
open import Structure.Setoid.WithLvl using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Type

module One {ℓ} {T : Type{ℓ}} where
  [≡]-reflexivity-raw : Names.Reflexivity (_≡_ {T = T})
  [≡]-reflexivity-raw = [≡]-intro

  [≡]-symmetry-raw : Names.Symmetry (_≡_ {T = T})
  [≡]-symmetry-raw [≡]-intro = [≡]-intro

  [≡]-transitivity-raw : Names.Transitivity (_≡_ {T = T})
  [≡]-transitivity-raw [≡]-intro [≡]-intro = [≡]-intro

  instance
    [≡]-reflexivity : Reflexivity (_≡_ {T = T})
    Reflexivity.proof([≡]-reflexivity) = [≡]-reflexivity-raw

  instance
    [≡]-symmetry : Symmetry (_≡_ {T = T})
    Symmetry.proof([≡]-symmetry) = [≡]-symmetry-raw

  instance
    [≡]-transitivity : Transitivity (_≡_ {T = T})
    Transitivity.proof([≡]-transitivity) = [≡]-transitivity-raw

  instance
    [≡]-equivalence : Equivalence (_≡_ {T = T})
    [≡]-equivalence = intro

  instance
    [≡]-equiv : Equiv{ℓ}(T)
    Equiv._≡_ [≡]-equiv = _≡_
    Equiv.equivalence [≡]-equiv = [≡]-equivalence

  [≡]-to-equivalence : ∀{ℓₗ}{x y : T} → (x ≡ y) → ⦃ equiv-T : Equiv{ℓₗ}(T) ⦄ → (_≡ₛ_ ⦃ equiv-T ⦄ x y)
  [≡]-to-equivalence([≡]-intro) = reflexivity(_≡ₛ_)

  instance
    [≡]-sub-of-reflexive : ∀{ℓₗ}{_▫_ : T → T → Stmt{ℓₗ}} → ⦃ _ : Reflexivity(_▫_) ⦄ → ((_≡_) ⊆₂ (_▫_))
    _⊆₂_.proof [≡]-sub-of-reflexive [≡]-intro = reflexivity(_)
open One public

module Two {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} where
  -- Applies a function to each side of the equality (TODO: Remove this and use Function everywhere instead)
  [≡]-with : (f : A → B) → ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f [≡]-intro = [≡]-intro

  [≡]-function : ∀{f} → Function(f)
  Function.congruence([≡]-function {f}) eq = [≡]-with(f) eq

  instance
    [≡]-to-function : ∀{ℓₗ} → ⦃ equiv-B : Equiv{ℓₗ}(B) ⦄ → ∀{f : A → B} → Function ⦃ [≡]-equiv ⦄ ⦃ equiv-B ⦄ (f)
    Function.congruence ([≡]-to-function) [≡]-intro = reflexivity(_≡ₛ_)
open Two public

module Three {ℓ₁}{A : Type{ℓ₁}} {ℓ₂}{B : Type{ℓ₂}} {ℓ₃}{C : Type{ℓ₃}} where
  -- Applies an operation to each side of the equality (TODO: Make this an instance of BinaryOperator instead)
  [≡]-with-op : (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
  [≡]-with-op (_▫_) [≡]-intro [≡]-intro = [≡]-intro
  -- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
  --   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with(x ↦ (x ▫ b₁)) (a₁≡a₂))

  instance
    [≡]-binary-operator : ∀{_▫_} → BinaryOperator(_▫_)
    BinaryOperator.congruence([≡]-binary-operator {_▫_}) aeq beq = [≡]-with-op(_▫_) aeq beq
open Three public
