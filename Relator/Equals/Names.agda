module Relator.Equals.Names where

open import Logic
open import Relator.Equals
open import Type

module _ {ℓ} where
  -- A proof of equality is unique (using equality itself to determine uniqueness).
  -- Also called uniqueness of identity proofs or UIP.
  -- There is an axiom called "axiom UIP" which is a construction of the following type:
  -- • ∀{T} → UniqueIdentityProofs(T)
  UniqueIdentityProofs : Type{ℓ} → Stmt
  UniqueIdentityProofs(T) = ∀{x y : T}{eq₁ eq₂ : (x ≡ y)} → (eq₁ ≡ eq₂)

module _ {ℓ₁ ℓ₂} where
  -- Usage of the trivial equality reflexivity proof can be substituted by any proof of the same type.
  -- There is an axiom called "axiom K" which is a construction of the following type:
  -- • ∀{T} → IntroProofSubstitution(T)
  IntroProofSubstitution : Type{ℓ₁} → Stmt
  IntroProofSubstitution(T) = ∀{x : T}{P : (x ≡ x) → Type{ℓ₂}} → P([≡]-intro) → ∀{eq : (x ≡ x)} → P(eq)
