module Type.Isomorphism.Equiv where

open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type.Isomorphism
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  [≍]-reflexivity-raw : T ≍ T
  [≍]-reflexivity-raw = [∃]-intro _ ⦃ id-inversePair ⦄

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  [≍]-symmetry-raw : (A ≍ B) → (B ≍ A)
  [≍]-symmetry-raw _ = [∃]-intro _ ⦃ sym-inversePair ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  ⦃ func-ba : ∀{f : B → A} → Function(f) ⦄
  ⦃ func-bc : ∀{f : B → C} → Function(f) ⦄
  where

  [≍]-transitivity-raw : (A ≍ B) → (B ≍ C) → (A ≍ C)
  [≍]-transitivity-raw ([∃]-intro _ ⦃ p ⦄) ([∃]-intro _ ⦃ q ⦄) = [∃]-intro _ ⦃ trans-inversePair ⦃ inv₁ = p ⦄ ⦃ inv₂ = q ⦄ ⦄

module _ ⦃ equiv : ∀{T : Type{ℓ}} → Equiv{ℓₑ}(T) ⦄ where
  [≍]-reflexivity : Reflexivity{T = Type{ℓ}}(\A B → (A ≍ B))
  [≍]-reflexivity = intro [≍]-reflexivity-raw

  [≍]-symmetry : Symmetry{T = Type{ℓ}}(\A B → (A ≍ B))
  [≍]-symmetry = intro [≍]-symmetry-raw

  module _ ⦃ func : ∀{A B : Type{ℓ}}{f : A → B} → Function(f) ⦄ where
    [≍]-transitivity : Transitivity{T = Type{ℓ}}(\A B → (A ≍ B))
    [≍]-transitivity = intro [≍]-transitivity-raw

    [≍]-equivalence : Equivalence{T = Type{ℓ}}(\A B → (A ≍ B))
    [≍]-equivalence = intro ⦃ [≍]-reflexivity ⦄ ⦃ [≍]-symmetry ⦄ ⦃ [≍]-transitivity ⦄

    Type-equiv : Equiv(Type{ℓ})
    Type-equiv = intro(\A B → (A ≍ B)) ⦃ [≍]-equivalence ⦄
