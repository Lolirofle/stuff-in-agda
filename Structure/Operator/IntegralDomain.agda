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

private variable ℓ ℓₑ : Lvl.Level

module _ where
  private variable T : Type{ℓ}
  private variable x y : T

  -- When an Rg have no non-zero zero divisors.
  -- Alternatively: All elements except zero are regular divisors.
  -- Also called: Zero-product property, rule of zero product, null factor law, multiplication property of zero, nonexistence of nontrivial zero divisors, zero-factor property.
  record Regular ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rg : Rg(_+_)(_⋅_) ⦄ : Stmt{Lvl.of(T) Lvl.⊔ ℓₑ} where
    constructor intro
    open Rg(rg)
    field
      no-zero-divisors  : (x ⋅ y ≡ 𝟎) → ((x ≡ 𝟎) ∨ (y ≡ 𝟎))

    zero-zero-divisorₗ : ZeroDivisorₗ(x) → (x ≡ 𝟎)
    zero-zero-divisorₗ {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 xy𝟎 ⦄) = [∨]-elim id ([⊥]-elim ∘ y𝟎) (no-zero-divisors xy𝟎)

    zero-zero-divisorᵣ : ZeroDivisorᵣ(x) → (x ≡ 𝟎)
    zero-zero-divisorᵣ {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 xy𝟎 ⦄) = [∨]-elim ([⊥]-elim ∘ y𝟎) id (no-zero-divisors xy𝟎)

    zero-zero-divisor : ZeroDivisor(x) → (x ≡ 𝟎)
    zero-zero-divisor {x} ([∃]-intro y ⦃ [∧]-intro y𝟎 ([∧]-intro xy𝟎 yx𝟎) ⦄) = [∨]-elim id ([⊥]-elim ∘ y𝟎) (no-zero-divisors xy𝟎)

  -- Non-trivial ring that has no non-zero zero divisors.
  record Domain ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{Lvl.of(T) Lvl.⊔ ℓₑ} where
    constructor intro
    field ⦃ ring ⦄ : Ring(_+_)(_⋅_)
    open Ring(ring) public
    field ⦃ regular ⦄ : Regular(_+_)(_⋅_)
    open Regular ⦃ rg = rg ⦄ regular public
    field
      ⦃ distinct-identities ⦄ : DistinctIdentities

  -- Non-trivial commutative ring and domain.
  record IntegralDomain ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{Lvl.of(T) Lvl.⊔ ℓₑ} where
    constructor intro
    field ⦃ ring ⦄ : Ring(_+_)(_⋅_)
    open Ring(ring) public
    field ⦃ regular ⦄ : Regular(_+_)(_⋅_)
    open Regular ⦃ rg = rg ⦄ regular public
    field
      ⦃ [⋅]-commutativity ⦄ : Commutativity(_⋅_)
      ⦃ distinct-identities ⦄ : DistinctIdentities

record IntegralDomainObject : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ integralDomain ⦄ : IntegralDomain(_+_)(_⋅_)
  open IntegralDomain(integralDomain) public
