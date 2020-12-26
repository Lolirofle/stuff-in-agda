import      Lvl
open import Type

module Type.Cardinality.Proofs {ℓₗ : Lvl.Level} where

open import Functional
import      Logic.Predicate
import      Logic.Predicate.Theorems
import      Relator.Equals
import      Relator.Equals.Proofs
import      Type.Cardinality
import      Type.Functions
import      Type.Functions.Proofs
import      Type.Functions.Inverse
import      Type.Functions.Inverse.Proofs

module _ {ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  open Logic.Predicate               {ℓₗ}
  open Logic.Predicate.Theorems      {ℓₗ}
  open Type.Cardinality              {ℓₗ}
  open Type.Functions                {ℓₗ}
  open Type.Functions.Inverse        {ℓₗ}
  open Type.Functions.Inverse.Proofs {ℓₗ}
  open Type.Functions.Proofs         {ℓₗ}

  instance
    [≍]-to-[≼] : ⦃ _ : X ≍ Y ⦄ → (X ≼ Y)
    [≍]-to-[≼] ⦃ proof ⦄ = [∃]-map (proof ↦ bijective-to-injective ⦃ proof ⦄) proof

  instance
    [≍]-to-[≽] : ⦃ _ : X ≍ Y ⦄ → (X ≼ Y)
    [≍]-to-[≽] ⦃ proof ⦄ = [∃]-map (proof ↦ bijective-to-injective ⦃ proof ⦄) proof

  [≍]-symmetry : (X ≍ Y) → (Y ≍ X)
  [≍]-symmetry ([∃]-intro f ⦃ proof ⦄) = [∃]-intro (inv f ⦃ proof ⦄) ⦃ inv-bijective {ℓₒ₁}{ℓₒ₂} {_}{_} {f} ⦃ proof ⦄ ⦄

  -- TODO: Is it possible to prove these?
  -- [≍]-antisymmetry : (X ≼ Y) → (X ≽ Y) → (X ≍ Y)
  -- [≍]-antisymmetry = [∃]-map ()

  -- [≼][≽]-swap : (X ≼ Y) → (Y ≽ X)
  -- [≽][≼]-swap : (X ≽ Y) → (Y ≼ X)

module _ {ℓₒ} {X : Type{ℓₒ}} where
  open Logic.Predicate          {ℓₗ Lvl.⊔ ℓₒ}
  open Logic.Predicate.Theorems {ℓₗ Lvl.⊔ ℓₒ}
  open Type.Cardinality         {ℓₗ Lvl.⊔ ℓₒ}
  open Type.Functions.Proofs     {ℓₗ Lvl.⊔ ℓₒ}

  instance
    [≍]-reflexivity : (X ≍ X)
    [≍]-reflexivity = [∃]-intro (id) ⦃ id-is-bijective ⦄

  instance
    [≼]-reflexivity : (X ≼ X)
    [≼]-reflexivity = [∃]-intro(id) ⦃ bijective-to-injective ⦃ id-is-bijective ⦄ ⦄

  instance
    [≽]-reflexivity : (X ≽ X)
    [≽]-reflexivity = [∃]-intro(id) ⦃ bijective-to-surjective ⦃ id-is-bijective ⦄ ⦄

module _ {ℓₒ} {X : Type{ℓₒ}} {Y : Type{ℓₒ}} where
  open Type.Cardinality {ℓₗ Lvl.⊔ ℓₒ}
  open Relator.Equals   {ℓₗ Lvl.⊔ ℓₒ}{Lvl.𝐒(ℓₒ)}

  [≡]-to-[≍] : (X ≡ Y) → (X ≍ Y)
  [≡]-to-[≍] [≡]-intro = [≍]-reflexivity
