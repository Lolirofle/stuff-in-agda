module Relator.Equals.Proofs where

import      Lvl
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Relator.Equals
open import Sets.Setoid using (Equiv ; intro ; Function ; BinaryOperator)
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type
-- import Type using () renaming (Type to Type)

module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} where
  -- Replaces occurrences of an element in a function
  [≡]-substitutionₗ : ∀{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) ← f(y)
  [≡]-substitutionₗ [≡]-intro = id

  -- Replaces occurrences of an element in a function
  [≡]-substitutionᵣ : ∀{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₂}} → f(x) → f(y)
  [≡]-substitutionᵣ [≡]-intro = id

  -- Note:
  --   The elimination rules can be used in different ways:
  --   • From (f(x) ∧ (x=y)) to f(y)
  --   • From f(x) to ((x=y) → f(y))
  -- ((x=y) → f(y)) cannot prove f(x) alone because of implication rules.

  [≡]-elimₗ = [≡]-substitutionₗ
  [≡]-elimᵣ = [≡]-substitutionᵣ

  [≡]-elim : ∀{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
  [≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

  [≡]-unelim : ∀{x y : T} → (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
  [≡]-unelim {x}{_} (F) = F {y ↦ (x ≡ y)} ([≡]-intro)

  -- I think this is called "Extensional equality" and cannot be proved?
  -- See:
  --   https://www.reddit.com/r/agda/comments/4te0rg/functors_extensional_equality_and_function/
  --   https://mathoverflow.net/questions/156238/function-extensionality-does-it-make-a-difference-why-would-one-keep-it-out-of
  -- [≡]-function : ∀{A B : Type}{f₁ f₂ : A → B) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

  -- Elimination rule for identity types.
  -- Also called J.
  -- This is interpreted as saying that all proofs of an equality are equal to each other. (TODO: Are they?)
  -- Explanation:
  --   P{x}{y} (eq-proof) is an arbitrary predicate with possible mentions of an equality proof.
  --   A value of type (∀{x : T} → P{x}{x}([≡]-intro)) means:
  --     [≡]-intro satisfies P for every pair with equal elements.
  --   The conclusion of type (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq)) means:
  --     Every equality proof satisfies P for every pair there is.
  -- TODO: https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
  -- TODO: Usage: https://stackoverflow.com/questions/22580842/non-trivial-negation-in-agda
  [≡]-identity-eliminator : (P : ∀{x y : T} → (x ≡ y) → Stmt{ℓ₂}) → (∀{x : T} → P{x}{x}([≡]-intro)) → (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq))
  [≡]-identity-eliminator _ proof {x}{.x} [≡]-intro = proof{x}

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
  [≡]-function-application : ∀{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
  [≡]-function-application [≡]-intro = [≡]-intro

  -- Applies a function to each side of the equality (TODO: Make this an instance of Function instead)
  [≡]-with : (f : A → B) → ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f [≡]-intro = [≡]-intro

  [≡]-with-specific : ∀{x y : A} → (f : (a : A) → ⦃ _ : (a ≡ x) ⦄ → ⦃ _ : (a ≡ y) ⦄ → B) → (p : (x ≡ y)) → (f(x) ⦃ [≡]-intro ⦄ ⦃ p ⦄ ≡ f(y) ⦃ symmetry(_≡_) p ⦄ ⦃ [≡]-intro ⦄)
  [≡]-with-specific f [≡]-intro = [≡]-intro

  -- [≢]-without : ∀{A : Type{ℓ₂}}{B : Type{ℓ₃}} → (f : A → B) → ∀{x y : A} → (f(x) ≢₃ f(y)) → (x ≢₂ y)
  -- [≢]-without f {_}{_} = liftᵣ([≡]-with f)

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
