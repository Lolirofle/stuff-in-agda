import      Lvl

module Structure.Relator.Ordering.Subsets {ℓₗ : Lvl.Level} {ℓₒ} {ℓₒₗ} where

open import Functional
open import Logic.Propositional
open import Sets.Subset{ℓₒ}{ℓₒ Lvl.⊔ ℓₒₗ}
import      Structure.Relator.Ordering
open import Type{ℓₒ Lvl.⊔ ℓₒₗ}

module Weak {T : Type} (_≤_ : T → T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) where
  open Structure.Relator.Ordering.Weak.Properties{ℓₒ Lvl.⊔ ℓₒₗ}{ℓₒ Lvl.⊔ ℓₒₗ} {T}(_≤_)

  -- LowerBounds(P) represents the set {x. P(x)}
  LowerBounds : (P : T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) → Type
  LowerBounds(P) = Subset{T}(l ↦ LowerBound(P)(l))

  -- Infinum(P) contains the supremum (inf(P)) of the set {x. P(x)} (The greatest lower bound of the set)
  record Infinum (P : T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) : Type where
    field
      inf : T
      ⦃ lowerBound ⦄ : LowerBound(P)(inf)
      greatestLowerbound : ∀{l} → LowerBound(P)(l) → (l ≤ inf)
  open Infinum {{...}} using (inf) public

  -- UpperBounds(P) represents the set {x. P(x)}
  UpperBounds : (P : T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) → Type
  UpperBounds(P) = Subset{T}(u ↦ UpperBound(P)(u))

  -- Supremum(P) contains the supremum (sup(P)) of the set {x. P(x)} (The least upper bound of the set)
  record Supremum (P : T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) : Type where
    field
      sup : T
      ⦃ upperBound ⦄ : UpperBound(P)(sup)
      leastUpperbound : ∀{u} → UpperBound(P)(u) → (sup ≤ u)
  open Supremum {{...}} using (sup) public
