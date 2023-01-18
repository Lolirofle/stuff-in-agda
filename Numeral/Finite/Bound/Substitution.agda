module Numeral.Finite.Bound.Substitution where

open import Data
open import BidirectionalFunction using (_↔_ ; intro ; _$ᵣ_)
open import Numeral.Finite
open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Numeral.Natural
open import Numeral.Natural.Proofs
open import Type.Identity
open import Type.Identity.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator
open import Structure.Relator.Properties

private variable N l r : ℕ
private variable n : 𝕟(N)
private variable eq eqₗ eqᵣ : Id l r

-- Id-substitution for 𝕟 that reduces to the identity function when pattern matched.
subst : Id l r → 𝕟(l) ↔ 𝕟(r)
subst eq = intro (R(symmetry(Id) eq)) (R eq) where
  R : Id l r → 𝕟(l) → 𝕟(r)
  R {𝐒 l}{𝐒 r} _  𝟎     = 𝟎
  R {𝐒 l}{𝐒 r} eq (𝐒 i) = 𝐒(R{l}{r} (injective ⦃ _ ⦄ ⦃ _ ⦄ (𝐒) {l}{r} eq) i)

subst-identity : (subst eq $ᵣ n) ≡ n
subst-identity {𝐒 l} {𝐒 r} {eq} {𝟎} = <>
subst-identity {𝐒 l} {𝐒 r} {eq} {𝐒 n} = subst-identity {l}{r}{injective ⦃ _ ⦄ ⦃ _ ⦄ (𝐒) {l}{r} eq}{n}

subst-nested-identity : (subst eqₗ $ᵣ (subst eqᵣ $ᵣ n)) ≡ n
subst-nested-identity {a}{b}{eqₗ}{c}{eqᵣ} {n} = [≡]-transitivity-raw {a = subst eqₗ $ᵣ (subst eqᵣ $ᵣ n)} (subst-identity{a}) (subst-identity{c})

instance
  subst-inverse : InversePair ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ (subst eq)
  InversePair.left (subst-inverse {eq = eq}) = intro(sub₂(_≡_)(Id) (subst-nested-identity{eqₗ = eq}{eqᵣ = symmetry(Id) eq}))
  InversePair.right(subst-inverse {eq = eq}) = intro(sub₂(_≡_)(Id) (subst-nested-identity{eqₗ = symmetry(Id) eq}{eqᵣ = eq}))

-- Substitution on 𝕟 by the cases of 𝕟.
instance
  𝕟-relator : UnaryRelator ⦃ Id-equiv ⦄ (𝕟)
  𝕟-relator = intro subst
