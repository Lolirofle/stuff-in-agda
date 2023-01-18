module Numeral.Natural.Inductions.Proofs where

open import Numeral.Natural
open import Numeral.Natural.Induction
open import Numeral.Natural.Inductions
open import Numeral.Natural.Relation.Order
open import Syntax.Function
open import Type

module _
  {ℓ₁ ℓ₂}
  (T : ℕ → Type{ℓ₁})
  (P : (x : ℕ) → T(x) → Type{ℓ₂})
  {rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
  (prec : (y : ℕ)
    → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion(T) rec x))
    → P y (ℕ-strong-recursion(T) rec y)
  )
  where

  ℕ-strong-recursion-simple-intro : (x : ℕ) → P x (ℕ-strong-recursion(T) rec x)
  ℕ-strong-recursion-simple-intro = ℕ-strong-recursion(x ↦ P x (ℕ-strong-recursion(T) rec x)) prec

open import Relator.Equals

module _
  {ℓ}
  (T : ℕ → Type{ℓ})
  {rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
  (pt : ∀{x}{t₁ t₂} → (∀{i}{ix₁ ix₂} → (t₁ i ix₁ ≡ t₂ i ix₂)) → (rec x t₁ ≡ rec x t₂))
  where

  ℕ-strong-recursion-internals-ext : ∀{x₁ x₂ i : ℕ}{ix₁ : i < x₁}{ix₂ : i < x₂} → (ℕ-strong-recursion-internals T rec x₁ i ix₁ ≡ ℕ-strong-recursion-internals T rec x₂ i ix₂)
  ℕ-strong-recursion-internals-ext {𝐒 x₁}{𝐒 x₂} {i} {ix₁} {ix₂} = pt(ℕ-strong-recursion-internals-ext{x₁}{x₂})

open import Data
open import DependentFunctional using () renaming (const to constDep)
open import Functional
open import Logic.Propositional.Equiv
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Inductions
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator
open import Structure.Relator.Properties

module _
  {ℓ₁ ℓ₂}
  (T : ℕ → Type{ℓ₁})
  (P : (n : ℕ) → ((i : ℕ) → (i < n) → T(i)) → Type{ℓ₂})
  {rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
  (pempty : P 𝟎 (\_ → empty ∘ [<][0]ᵣ))
  (prec : (y : ℕ) → ⦃ pos : Positive(y) ⦄
    → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion-internals(T) rec x))
    → P y (\z zy → rec z (\x xz → ℕ-strong-recursion-internals(T) rec (𝐏(y)) x (transitivity(_≤_) xz ([≤]-with-[𝐏] zy))))
  )
  where

  ℕ-strong-recursion-internals-intro : (N : ℕ) → (n : ℕ) → (n < N) → P n (\i ord → ℕ-strong-recursion-internals(T) rec n i ord)
  ℕ-strong-recursion-internals-intro = ℕ-strong-recursion-internals(\n → P n (ℕ-strong-recursion-internals T rec n)) (\{ 𝟎 → \_ → pempty ; (𝐒 n) → prec(𝐒 n) })

module _
  {ℓ₁ ℓ₂}
  (T : ℕ → Type{ℓ₁})
  (P : (x : ℕ) → T(x) → Type{ℓ₂})
  {rec : (x : ℕ) → ((i : ℕ) → (i < x) → T(i)) → T(x)}
  (pt : ∀{x}{t₁ t₂} → (∀{i}{ix₁ ix₂} → (t₁ i ix₁ ≡ t₂ i ix₂)) → (rec x t₁ ≡ rec x t₂))
  (prec : (y : ℕ)
    → ((x : ℕ) → (xy : x < y) → P x (ℕ-strong-recursion(T) rec x))
    → P y (rec y (\x _ → ℕ-strong-recursion(T) rec x))
  )
  where

  ℕ-strong-recursion-intro : (x : ℕ) → P x (ℕ-strong-recursion(T) rec x)
  ℕ-strong-recursion-intro = ℕ-strong-recursion
    (x ↦ P x (ℕ-strong-recursion(T) rec x))
    (\x px → substitute₁ᵣ(P x) (pt(\{i} → ℕ-strong-recursion-internals-ext(T) pt {𝐒 i}{x}{i}{reflexivity(_≤_)})) (prec x px))
