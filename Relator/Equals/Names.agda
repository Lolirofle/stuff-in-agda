module Relator.Equals.Names where

open import Logic
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Type
open import Type.Size

module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} where
  IdentityEliminator : Stmt
  IdentityEliminator = (P : ∀{x y : T} → (x ≡ y) → Stmt{ℓ₂}) → (∀{x : T} → P{x}{x}([≡]-intro)) → (∀{x y : T} → (eq : (x ≡ y)) → P{x}{y}(eq))

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

module _ {ℓ} {A : Type{ℓ}} {B : Type{ℓ}} where
  -- There is a bijection between proofs of equalities and proofs of bijections for types.
  Univalence : Stmt
  Univalence = (A ≡ B) ≍ (A ≍ B)

-- TODO: ComputablyDecidable → UIP (https://homotopytypetheory.org/2012/03/30/a-direct-proof-of-hedbergs-theorem/)
