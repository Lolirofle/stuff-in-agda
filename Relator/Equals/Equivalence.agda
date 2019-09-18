module Relator.Equals.Equivalence where

import      Lvl
open import Lang.Instance
open import Logic
open import Relator.Equals
open import Sets.Setoid using (Equiv ; intro ; Function ; BinaryOperator)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _ {ℓ} {T : Type{ℓ}} where
  instance
    [≡]-reflexivity : Reflexivity (_≡_ {T = T})
    Reflexivity.proof([≡]-reflexivity) = [≡]-intro

  instance
    [≡]-symmetry : Symmetry (_≡_ {T = T})
    Symmetry.proof([≡]-symmetry) [≡]-intro = [≡]-intro

  instance
    [≡]-transitivity : Transitivity (_≡_ {T = T})
    Transitivity.proof([≡]-transitivity) [≡]-intro [≡]-intro = [≡]-intro

  instance
    [≡]-equivalence : Equivalence (_≡_ {T = T})
    Equivalence.reflexivity ([≡]-equivalence) = infer
    Equivalence.symmetry    ([≡]-equivalence) = infer
    Equivalence.transitivity([≡]-equivalence) = infer

  instance
    [≡]-equiv : Equiv(T)
    [≡]-equiv = Equiv.intro(_≡_ {T = T}) ⦃ [≡]-equivalence ⦄

  [≡]-to-equivalence : ∀{x y : T} → (x ≡ y) → ⦃ eq : Equiv(T) ⦄ → let Equiv.intro(_≡ₛ_) = eq in (x ≡ₛ y)
  [≡]-to-equivalence([≡]-intro) ⦃ intro(_≡ₛ_) ⦄ = reflexivity(_≡ₛ_)

module _ {ℓ₁}{ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} where
  -- Applies a function to each side of the equality (TODO: Make this an instance of Function instead)
  [≡]-with : (f : A → B) → ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f [≡]-intro = [≡]-intro

  instance
    [≡]-function : ∀{f} → Function(f)
    Function.congruence([≡]-function {f}) eq = [≡]-with(f) eq

module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} where
  -- Applies an operation to each side of the equality (TODO: Make this an instance of BinaryOperator instead)
  [≡]-with-op : (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
  [≡]-with-op (_▫_) [≡]-intro [≡]-intro = [≡]-intro
  -- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
  --   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with(x ↦ (x ▫ b₁)) (a₁≡a₂))

  instance
    [≡]-binary-operator : ∀{_▫_} → BinaryOperator(_▫_)
    BinaryOperator.congruence([≡]-binary-operator {_▫_}) aeq beq = [≡]-with-op(_▫_) aeq beq
