module Data.List.Relation.Pairwise.Proofs where

open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Pairwise
open import Logic
import      Lvl
open import Type

private variable ℓ ℓₗ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x : T
private variable f : A → B
private variable _▫_ : T → T → Type{ℓₗ}
private variable _▫₁_ : A → A → Type{ℓₗ}
private variable _▫₂_ : B → B → Type{ℓₗ}

AdjacentlyPairwise-map : (∀{x y} → (x ▫₁ y) → (f(x) ▫₂ f(y))) → ∀{l} → AdjacentlyPairwise(_▫₁_)(l) → AdjacentlyPairwise(_▫₂_)(List.map f(l))
AdjacentlyPairwise-map p {∅} s = AdjacentlyPairwise.empty
AdjacentlyPairwise-map p {x ⊰ ∅} s = AdjacentlyPairwise.single
AdjacentlyPairwise-map p {x ⊰ y ⊰ l} (AdjacentlyPairwise.step ⦃ s₁ ⦄ ⦃ s₂ ⦄) = AdjacentlyPairwise.step ⦃ p s₁ ⦄ ⦃ AdjacentlyPairwise-map p {y ⊰ l} s₂ ⦄

AdjacentlyPairwise-prepend : (∀{y} → (x ▫ y)) → ∀{l} → AdjacentlyPairwise(_▫_)(l) → AdjacentlyPairwise(_▫_)(x ⊰ l)
AdjacentlyPairwise-prepend xy {∅}     p = AdjacentlyPairwise.single
AdjacentlyPairwise-prepend xy {_ ⊰ _} p = AdjacentlyPairwise.step ⦃ xy ⦄ ⦃ p ⦄
