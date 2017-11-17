module Relator.Equals.Theorems {ℓ₁}{ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Relator.Equivalence{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type
-- import Type using () renaming (Type to Type)

module _ {ℓ₃} where
  -- Replaces occurrences of an element in a function
  [≡]-substitutionₗ : ∀{T}{x y : T} → (x ≡ y) → ∀{f : T → Type{ℓ₃}} → f(x) ← f(y)
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

{-
[≡]-elim-stmtₗ : ∀{T}{X Y : Stmt} → (X ≡ Y) → X ← Y
[≡]-elim-stmtₗ = [≡]-substitutionₗ

[≡]-elim-stmtᵣ : ∀{T}{X Y : Stmt} → (X ≡ Y) → X → Y
[≡]-elim-stmtᵣ = [≡]-substitutionₗ
-}

instance
  [≡]-reflexivity : ∀{T} → Reflexivity {T} (_≡_ {T})
  reflexivity{{[≡]-reflexivity}} = [≡]-intro

instance
  [≡]-symmetry : ∀{T} → Symmetry {T} (_≡_ {T})
  symmetry{{[≡]-symmetry}} [≡]-intro = [≡]-intro

instance
  [≡]-transitivity : ∀{T} → Transitivity {T} (_≡_ {T})
  transitivity{{[≡]-transitivity}} ([∧]-intro [≡]-intro [≡]-intro) = [≡]-intro

-- Applies a function to each side of the equality (TODO: Maybe rename to [≡]-apply?)
[≡]-with-[_] : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro
{-
[≡]-with-[_] : ∀{T₁ : Type{ℓ₂}}{T₂ : Type{ℓ₃}} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with-[_] f [≡]-intro = [≡]-intro
-}

[≢]-without-[_] : ∀{T₁ T₂} → (f : T₁ → T₂) → ∀{x : T₁}{y : T₁} → (f(x) ≢ f(y)) → (x ≢ y)
[≢]-without-[_] f {_}{_} = liftᵣ([≡]-with-[_] f)

-- Applies an operation to each side of the equality
[≡]-with-op-[_] : ∀{A B C : Type} → (_▫_ : A → B → C) → {a₁ a₂ : A}{b₁ b₂ : B} → (a₁ ≡ a₂) → (b₁ ≡ b₂) → ((a₁ ▫ b₁) ≡ (a₂ ▫ b₂))
[≡]-with-op-[_] (_▫_) [≡]-intro [≡]-intro = [≡]-intro
-- [≡]-with-op-[_] (_▫_) {a₁}{a₂} {b₁}{b₂} (a₁≡a₂) (b₁≡b₂) =
--   [≡]-elimᵣ (b₁≡b₂) {\x → (a₁ ▫ b₁) ≡ (a₂ ▫ x)} ([≡]-with-[(x ↦ (x ▫ b₁))] (a₁≡a₂))

instance
  [≡]-equivalence : ∀{T} → Equivalence {T} (_≡_ {T})
  Equivalence.reflexivity ([≡]-equivalence) = infer
  Equivalence.symmetry    ([≡]-equivalence) = infer
  Equivalence.transitivity([≡]-equivalence) = infer

[≡]-function-application : ∀{A B : Type}{f₁ f₂ : A → B} → (f₁ ≡ f₂) → (∀{x} → (f₁(x) ≡ f₂(x)))
[≡]-function-application [≡]-intro = [≡]-intro

-- I think this is called "Extentional equality" and cannot be proved?
-- See:
--   https://www.reddit.com/r/agda/comments/4te0rg/functors_extensional_equality_and_function/
--   https://mathoverflow.net/questions/156238/function-extensionality-does-it-make-a-difference-why-would-one-keep-it-out-of
-- [≡]-function : ∀{T₁ T₂ : Type}{f₁ f₂ : T₁ → T₂) → (∀{x} → (f₁(x) ≡ f₂(x))) → (f₁ ≡ f₂)

[≡]-intro-[→] : ∀{T}{x y : T}{f : T → Stmt} → f(x) → ((x ≡ y) → f(y))
[≡]-intro-[→] {T}{x}{y}{f} fx xy = [≡]-elimᵣ {T}{x}{y} xy {f} fx
