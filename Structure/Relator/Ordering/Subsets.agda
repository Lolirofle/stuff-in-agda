import Lvl

module Structure.Relator.Ordering.Subsets {ℓₗ : Lvl.Level} {ℓₒ} {ℓₒₗ} where

open import Functional
open import Logic.Propositional
open import Logic.Predicate{ℓₒ}{ℓₒ Lvl.⊔ ℓₒₗ}
open import Sets.PredicateSet.Filter{ℓₒ}{ℓₒ Lvl.⊔ ℓₒₗ}
import      Structure.Relator.Ordering
open import Type{ℓₒ Lvl.⊔ ℓₒₗ}

module Weak {T : Type} (_≤_ : T → T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) where
  open Structure.Relator.Ordering.Weak.Properties{ℓₒ Lvl.⊔ ℓₒₗ}{ℓₒ Lvl.⊔ ℓₒₗ} {T}(_≤_)

  module _ (P : T → Stmt{ℓₒ Lvl.⊔ ℓₒₗ}) where
    -- LowerBound(P)(x) represents that x is a lower bound of the set {x. P(x)}
    record LowerBound (l : T) : Type where
      field
        lowerBound : ∀{x} → P(x) → (l ≤ x)

    -- LowerBounds(P) represents the set {x. P(x)}
    LowerBounds : Type
    LowerBounds = Filter{T}(l ↦ LowerBound(l))

    -- Infinum(P) contains the supremum (inf(P)) of the set {x. P(x)} (The greatest lower bound of the set)
    record Infinum (inf : T) : Type where
      field
        ⦃ lowerBound ⦄ : LowerBound(inf)
        greatestLowerbound : ∀{l} → LowerBound(l) → (l ≤ inf)

    inf : ⦃ _ : ∃(Infinum) ⦄ → T
    inf ⦃ e ⦄ = [∃]-witness e

    -- UpperBound(P)(x) represents that x is an upper bound of the set {x. P(x)}
    record UpperBound (u : T) : Type where
      field
        upperBound : ∀{x} → P(x) → (x ≤ u)

    -- UpperBounds(P) represents the set {x. P(x)}
    UpperBounds : Type
    UpperBounds = Filter{T}(u ↦ UpperBound(u))

    -- Supremum(P) contains the supremum (sup(P)) of the set {x. P(x)} (The least upper bound of the set)
    record Supremum (sup : T) : Type where
      field
        ⦃ upperBound ⦄ : UpperBound(sup)
        leastUpperbound : ∀{u} → UpperBound(u) → (sup ≤ u)

    sup : ⦃ _ : ∃(Supremum) ⦄ → T
    sup ⦃ e ⦄ = [∃]-witness e
