module Structure.Operator.Group {ℓ₁} {ℓ₂} where

open import Functional hiding (id)
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Sets.Setoid{ℓ₁}
open import Structure.Operator.Monoid{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- A type and a binary operator using this type is a group when:
-- • It is a monoid.
-- • The operator have an inverse in both directions.
record Group {T : Type} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt where
  open Monoid ⦃ ... ⦄

  field
    inv : T → T
  field
    instance ⦃ monoid ⦄ : Monoid{T} (_▫_)
    inverse : InverseFunction (_▫_) (id ⦃ _ ⦄ ⦃ monoid ⦄) inv

  inverseₗ : InverseFunctionₗ (_▫_) (id ⦃ _ ⦄ ⦃ monoid ⦄) inv
  inverseₗ = [∧]-elimₗ inverse

  inverseᵣ : InverseFunctionᵣ (_▫_) (id ⦃ _ ⦄ ⦃ monoid ⦄) inv
  inverseᵣ = [∧]-elimᵣ inverse

-- Multiplicative Group (TODO: Use setoids to express this instead)
record MultGroup {T : Type} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) (𝟎 : T) : Stmt where
  open Monoid ⦃ ... ⦄

  field
    inv : (x : T) → ⦃ _ : (x ≢ 𝟎) ⦄ → T
  field
    instance ⦃ monoid ⦄ : Monoid{T} (_▫_)
    inverseₗ : ∀{x} → ⦃ nonzero : (x ≢ 𝟎) ⦄ → ((inv x ⦃ nonzero ⦄) ▫ x) ≡ id ⦃ _ ⦄ ⦃ monoid ⦄
    inverseᵣ : ∀{x} → ⦃ nonzero : (x ≢ 𝟎) ⦄ → (x ▫ (inv x ⦃ nonzero ⦄)) ≡ id ⦃ _ ⦄ ⦃ monoid ⦄

record CommutativeGroup {T : Type} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt where
  open Group ⦃ ... ⦄
  open Monoid ⦃ ... ⦄

  field
    instance ⦃ group ⦄ : Group (_▫_)
    commutativity : Commutativity (_▫_)

record Subgroup {S : Type} ⦃ _ : Equiv(S) ⦄ (_▫ₛ_ : S → S → S) {T : Type} ⦃ _ : Equiv(T) ⦄ (_▫ₜ_ : T → T → T) : Stmt where
  open Monoid ⦃ ... ⦄

  field
    instance ⦃ groupₗ ⦄ : Group{S}(_▫ₛ_)
    instance ⦃ groupᵣ ⦄ : Group{T}(_▫ₜ_)

  field
    instance size : (S ≼ T)

  field
    preserve-op : ∀{x y : S} → let μ = [∃]-witness(size) in (μ(x ▫ₛ y) ≡ μ(x) ▫ₜ μ(y))
