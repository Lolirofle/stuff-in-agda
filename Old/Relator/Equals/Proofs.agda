module Relator.Equals.Proofs {ℓ₁}{ℓ₂} where

import      Lvl
open import Functional
open import Lang.Instance
import      Logic.Propositional
import      Relator.Equals
open import Sets.Setoid{ℓ₁} using (Equiv)
import      Structure.Relator.Equivalence
import      Structure.Relator.Properties
open import Type
-- import Type using () renaming (Type to Type)

module _ where
  open Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
  open Relator.Equals{ℓ₁}{ℓ₂}
  open Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
  open Structure.Relator.Properties{ℓ₁}{ℓ₂}

  module _ {ℓ₃} where
    -- Replaces occurrences of an element in a function
    [≡]-substitutionₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₃}} → f(x) ←ᶠ f(y)
    [≡]-substitutionₗ [≡]-intro = id

    -- Replaces occurrences of an element in a function
    [≡]-substitutionᵣ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₃}} → f(x) → f(y)
    [≡]-substitutionᵣ [≡]-intro = id

  -- Note:
  --   The elimination rules can be used in different ways:
  --   • From (f(x) ∧ (x=y)) to f(y)
  --   • From f(x) to ((x=y) → f(y))
  -- ((x=y) → f(y)) cannot prove f(x) alone because of implication rules.

  [≡]-elimₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ← f(y)
  [≡]-elimₗ = [≡]-substitutionₗ

  [≡]-elimᵣ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) → f(y)
  [≡]-elimᵣ = [≡]-substitutionᵣ

  [≡]-elim : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Stmt} → f(x) ↔ f(y)
  [≡]-elim eq = [↔]-intro ([≡]-elimₗ eq) ([≡]-elimᵣ eq)

  [≡]-unelim : ∀{T}{x y : T} → (∀{f : T → Stmt} → f(x) → f(y)) → (x ≡ y)
  [≡]-unelim {_}{x}{_} (F) = F {y ↦ (x ≡ y)} ([≡]-intro)

  instance
    [≡]-reflexivity : ∀{T} → Reflexivity {T} (_≡_ {T})
    reflexivity ⦃ [≡]-reflexivity ⦄ = [≡]-intro

  instance
    [≡]-symmetry : ∀{T} → Symmetry {T} (_≡_ {T})
    symmetry ⦃ [≡]-symmetry ⦄ [≡]-intro = [≡]-intro

  instance
    [≡]-transitivity : ∀{T} → Transitivity {T} (_≡_ {T})
    transitivity ⦃ [≡]-transitivity ⦄ [≡]-intro [≡]-intro = [≡]-intro

  instance
    [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
    Equivalence.reflexivity ([≡]-equivalence) = infer
    Equivalence.symmetry    ([≡]-equivalence) = infer
    Equivalence.transitivity([≡]-equivalence) = infer

  -- I think this is called "Extensional equality" and cannot be proved?
  -- See:
  --   https://www.reddit.com/r/agda/comments/4te0rg/functors_extensional_equality_and_function/
  --   https://mathoverflow.net/questions/156238/function-extensionality-does-it-make-a-difference-why-would-one-keep-it-out-of
  -- [≡]-function : ∀{T₁ T₂ : Type}{f₁ f₂ : T₁ → T₂) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

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
  [≡]-identity-eliminator : ∀{T : Type} → (P : ∀{x y : T} → (x ≡ y) → Stmt) → (∀{x : T} → P{x}{x}([≡]-intro)) → (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq))
  [≡]-identity-eliminator _ proof {x}{.x} [≡]-intro = proof{x}

  instance
    [≡]-equiv : ∀{T} → Equiv(T)
    [≡]-equiv{T} = Equiv.intro(_≡_ {T})

module _ where
  open Logic.Propositional
  open Relator.Equals
  open Structure.Relator.Equivalence
  open Structure.Relator.Properties

  module _ {ℓ₃} where
    private _≡₂_ = _≡_ {ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
    private _≡₃_ = _≡_ {ℓ₁ Lvl.⊔ ℓ₃}{ℓ₃}
    private _≡₂₃_ = _≡_ {ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}{ℓ₂ Lvl.⊔ ℓ₃}

    private _≢₂_ = _≢_ {ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}
    private _≢₃_ = _≢_ {ℓ₁ Lvl.⊔ ℓ₃}{ℓ₃}
    private _≢₂₃_ = _≢_ {ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}{ℓ₂ Lvl.⊔ ℓ₃}

    [≡]-function-application : ∀{A : Type{ℓ₂}}{B : Type{ℓ₃}}{f₁ f₂ : A → B} → (f₁ ≡₂₃ f₂) → (∀{x} → (f₁(x) ≡₃ f₂(x)))
    [≡]-function-application [≡]-intro = [≡]-intro

    -- Applies a function to each side of the equality
    [≡]-with : ∀{T₁ : Type{ℓ₂}}{T₂ : Type{ℓ₃}} → (f : T₁ → T₂) → ∀{x y : T₁} → (x ≡₂ y) → (f(x) ≡₃ f(y))
    [≡]-with f [≡]-intro = [≡]-intro

    [≡]-with-specific : ∀{T₁ : Type{ℓ₂}}{T₂ : Type{ℓ₃}} → ∀{x y : T₁} → (f : (a : T₁) → ⦃ _ : (a ≡₂ x) ⦄ → ⦃ _ : (a ≡₂ y) ⦄ → T₂) → (p : (x ≡₂ y)) → (f(x) ⦃ [≡]-intro ⦄ ⦃ p ⦄ ≡₃ f(y) ⦃ symmetry p ⦄ ⦃ [≡]-intro ⦄)
    [≡]-with-specific f [≡]-intro = [≡]-intro

    -- [≢]-without : ∀{T₁ : Type{ℓ₂}}{T₂ : Type{ℓ₃}} → (f : T₁ → T₂) → ∀{x y : T₁} → (f(x) ≢₃ f(y)) → (x ≢₂ y)
    -- [≢]-without f {_}{_} = liftᵣ([≡]-with f)

    module _ {ℓ₄} where
      private _≡₄_ = _≡_ {ℓ₁ Lvl.⊔ ℓ₄}{ℓ₄}
      private _≢₄_ = _≢_ {ℓ₁ Lvl.⊔ ℓ₄}{ℓ₄}

      -- Applies an operation to each side of the equality
      [≡]-with-op : ∀{A : Type{ℓ₂}}{B : Type{ℓ₃}}{C : Type{ℓ₄}} → (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡₂ a₂) → (b₁ ≡₃ b₂) → ((a₁ ▫ b₁) ≡₄ (a₂ ▫ b₂))
      [≡]-with-op (_▫_) [≡]-intro [≡]-intro = [≡]-intro
      -- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
      --   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with(x ↦ (x ▫ b₁)) (a₁≡a₂))

module _ where
  open Logic.Propositional
  open Relator.Equals

  private
    _≡₂_ = _≡_ {ℓ₂}
    _≡₁₂_ = _≡_ {ℓ₁ Lvl.⊔ ℓ₂}

  -- Also called K.
  -- There is also an axiom called "axiom K" which is a construction of the following type:
  -- • ∀{T} → [≡]-ProofEquality(T)
  [≡]-ProofIdentity : Type{ℓ₂} → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  [≡]-ProofIdentity(T) = ∀{x y : T}{eq₁ eq₂ : (x ≡₂ y)} → (eq₁ ≡₁₂ eq₂)
