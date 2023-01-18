{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Properties where

open import Functional
import      Lvl
open import Type
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type.Identity
open import Type.Identity.Proofs
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Type.Identity

private variable ℓ : Lvl.Level

-- A type is an identity path type when the path type is equivalent to the identity type.
-- This holds when the type is not a HIT (higher inductive type) (when there are no extra paths in the definition of the type).
record IdentityPathType (T : Type{ℓ}) : Type{ℓ} where
  field
    ⦃ sub ⦄ : Path{P = T} ⊆₂ Id{T = T}
    inverse : ∀{x y : T}{p : Id x y} → Path(sub₂(Path)(Id) (sub₂(Id)(Path) p)) p
    inverse2 : ∀{x y : T}{p : Path x y} → Path(sub₂(Id)(Path) (sub₂(Path)(Id) p)) p

  IdentityKEliminator-sub : ∀{ℓₚ} → IdentityKEliminator(Id{T = T}) {ℓₚ} → IdentityKEliminator(Path{P = T}) {ℓₚ}
  IdentityKEliminator-sub (intro kElim) = intro \P p eq → substitute₁ᵣ(P) inverse2 (kElim(P ∘ sub₂(Id)(Path)) p (sub₂(Path)(Id) eq))
