module Function.Inverseₗ where

import      Lvl
import      Data.Either as Either
open import Data.Either.Proofs
open import Lang.Inspect
open import Logic
open import Logic.Classical
-- open import Logic.Computability
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Function.Names using (_⊜_)
import      Function.Equals as FunctionEq
open import Function.Proofs
-- open import Function.Domains TODO: Unapply
open import Structure.Setoid
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- TODO: Move to Function.Domains
module _ {ℓₒ₁ ℓₒ₂ : Lvl.Level} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}}  ⦃ eqY : Equiv(Y) ⦄ where
  record Unapply (f : X → Y) (y : Y) (x : X) : Type{ℓₒ₂} where
    constructor intro
    field ⦃ proof ⦄ : (f(x) ≡ y)

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} ⦃ eqA : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ eqB : Equiv(B) ⦄ where
  -- An inverse function of an injective function f.
  -- This is definable when the proposition "y is a value in f" for any y is decidable.
  -- Because f is not guaranteed to be surjective, all non-values in the codomain B use the fallback function to make the inverse a total (B → A).
  invₗ : (B → A) → (f : A → B) → ⦃ _ : ∀{y} → Classical(∃(Unapply f(y))) ⦄ → (B → A)
  invₗ(fallback) f(y) = Either.map1 [∃]-witness (const(fallback(y))) (excluded-middle{P = ∃(Unapply f(y))})
  -- {-# INLINE invₗ #-}

  module _ {fallback : B → A} {f : A → B} ⦃ classical-unapply : ∀{y} → Classical(∃(Unapply f(y))) ⦄ where
    invₗ-inverseₗ : ⦃ _ : Injective(f) ⦄ → (invₗ(fallback) (f) ∘ f ⊜ id)
    invₗ-inverseₗ{x} with excluded-middle{P = ∃(Unapply f(f(x)))} | inspect(invₗ(fallback) f) (f(x))
    ... | [∨]-introₗ ([∃]-intro _ ⦃ intro ⦃ p ⦄ ⦄) | _ = injective(f) p
    ... | [∨]-introᵣ p | _ = [⊥]-elim(p ([∃]-intro x ⦃ intro ⦃ proof = reflexivity(_≡_) ⦄ ⦄))

    [∘]-inverseₗ : ⦃ _ : Injective(f) ⦄ → ∃(g ↦ (g ∘ f ⊜ id))
    [∘]-inverseₗ = [∃]-intro(invₗ(fallback) f) ⦃ invₗ-inverseₗ ⦄

    invₗ-function : ⦃ _ : Function(fallback)⦄ → ⦃ _ : Function(f) ⦄ → Function(invₗ(fallback) f)
    Function.congruence invₗ-function {y₁}{y₂} y₁y₂ with excluded-middle{P = ∃(Unapply f(y₁))} | inspect(invₗ(fallback) f) y₁ | excluded-middle{P = ∃(Unapply f(y₂))} | inspect(invₗ(fallback) f) y₂
    ... | [∨]-introₗ ([∃]-intro x₁ ⦃ intro ⦃ p₁ ⦄ ⦄) | intro pp₁ | [∨]-introₗ ([∃]-intro x₂ ⦃ intro ⦃ p₂ ⦄ ⦄) | intro pp₂ = symmetry(_≡_) pp₁ 🝖 proof-test 🝖 pp₂ where -- TODO: Requires that Either.map1 is a function/operation
    -- Classical.excluded-middle classical-unapply
    -- {f₁ = [∃]-witness {Pred = Unapply f(y₂)}}
    -- map1-eq (reflexivity(_≡_)) (congruence₁(const) ⦃ const-function-function ⦃ ? ⦄ ⦄ (congruence₁(fallback) y₁y₂))
      proof-test :
        (Either.map1
          {ℓ₁ Lvl.⊔ ℓ₂} {∃ {ℓ₁} {ℓ₂} {A} (Unapply {ℓ₁} {ℓ₂} {A} {B} ⦃ eqB ⦄ f y₁)}
          {ℓ₁} {A}
          {ℓ₁ Lvl.⊔ ℓ₂} {∃ {ℓ₁} {ℓ₂} {A} (Unapply {ℓ₁} {ℓ₂} {A} {B} ⦃ eqB ⦄ f y₁) → ⊥}
          [∃]-witness
          (λ _ → fallback y₁)
          (Classical.excluded-middle (classical-unapply {y₁}))
        )
        ≡
        (Either.map1
          {ℓ₁ Lvl.⊔ ℓ₂} {∃ {ℓ₁} {ℓ₂} {A} (Unapply {ℓ₁} {ℓ₂} {A} {B} ⦃ eqB ⦄ f y₂)}
          {ℓ₁} {A}
          {ℓ₁ Lvl.⊔ ℓ₂} {∃ {ℓ₁} {ℓ₂} {A} (Unapply {ℓ₁} {ℓ₂} {A} {B} ⦃ eqB ⦄ f y₂) → ⊥}
          [∃]-witness
          (λ _ → fallback y₂)
          (Classical.excluded-middle (classical-unapply {y₂}))
        )
      proof-test = map1-eq {f₁ = {![∃]-witness!}} (reflexivity(_≡_)) (congruence₁(const) ⦃ const-function-function {c = x₁} ⦄ (congruence₁(fallback) y₁y₂)) {!!}
    ... | [∨]-introₗ([∃]-intro x₁ ⦃ intro ⦃ p₁ ⦄ ⦄) | intro pp₁ | [∨]-introᵣ np₂ | intro pp₂ with () ← np₂([∃]-intro(x₁) ⦃ intro ⦃ proof = p₁ 🝖 y₁y₂ ⦄ ⦄)
    ... | [∨]-introᵣ np₁ | intro pp₁ | [∨]-introₗ([∃]-intro x₂ ⦃ intro ⦃ p₂ ⦄ ⦄) | intro pp₂ with () ← np₁([∃]-intro(x₂) ⦃ intro ⦃ proof = p₂ 🝖 symmetry(_≡_) y₁y₂ ⦄ ⦄)
    ... | [∨]-introᵣ np₁ | intro pp₁ | [∨]-introᵣ np₂ | intro pp₂ = congruence₁(fallback) y₁y₂
