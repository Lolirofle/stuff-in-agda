module Structure.Operator.IntegralDomain where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Type

-- Rng with no non-zero zero divisors.
record Domain {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rng : Rng(_+_)(_⋅_) ⦄ : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  open Rng(rng)
  field
    no-zero-divisors  : ∀{x y} → (x ⋅ y ≡ 𝟎) → ((x ≡ 𝟎) ∨ (y ≡ 𝟎))

  zero-zero-divisorₗ : ∀{x} → ZeroDivisorₗ(x) → (x ≡ 𝟎)
  zero-zero-divisorₗ {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 xy𝟎 ⦄) = [∨]-elim id ([⊥]-elim ∘ y𝟎) (no-zero-divisors xy𝟎)

  zero-zero-divisorᵣ : ∀{x} → ZeroDivisorᵣ(x) → (x ≡ 𝟎)
  zero-zero-divisorᵣ {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 xy𝟎 ⦄) = [∨]-elim ([⊥]-elim ∘ y𝟎) id (no-zero-divisors xy𝟎)

  zero-zero-divisor : ∀{x} → ZeroDivisor(x) → (x ≡ 𝟎)
  zero-zero-divisor {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 ([∧]-intro xy𝟎 yx𝟎) ⦄) = [∨]-elim id ([⊥]-elim ∘ y𝟎) (no-zero-divisors xy𝟎)

-- Non-trivial commutative ring and domain.
record IntegralDomain {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ ring ⦄              : Ring(_+_)(_⋅_)
    ⦃ domain ⦄            : Domain(_+_)(_⋅_)
    ⦃ [⋅]-commutativity ⦄ : Commutativity(_⋅_)
  open Ring  (ring)   public
  open Domain(domain) public

  field
    ⦃ distinct-identities ⦄ : DistinctIdentities

record IntegralDomainObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ integralDomain ⦄ : IntegralDomain(_+_)(_⋅_)
  open IntegralDomain(integralDomain) public
