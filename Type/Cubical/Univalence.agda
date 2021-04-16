{-# OPTIONS --cubical #-}

module Type.Cubical.Univalence where

open import Function.Axioms
open import Functional
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function.Domain using (intro ; Inverseₗ ; Inverseᵣ)
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Type.Cubical.Path.Equality
open import Type.Cubical.Equiv
open import Type.Cubical
open import Type.Properties.MereProposition
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B P Q : Type{ℓ}

-- TODO: Move
primitive primGlue : (A : Type{ℓ₁}) → ∀{i : Interval} → (T : Interval.Partial i (Type{ℓ₂})) → (e : Interval.PartialP i (\o → T(o) ≍ A)) → Type{ℓ₂}

type-extensionalityₗ : (A ≡ B) ← (A ≍ B)
type-extensionalityₗ {A = A}{B = B} ab i = primGlue(B)
  (\{(i = Interval.𝟎) → A  ; (i = Interval.𝟏) → B})
  (\{(i = Interval.𝟎) → ab ; (i = Interval.𝟏) → reflexivity(_≍_)})

module _ ⦃ prop-P : MereProposition{ℓ}(P) ⦄ ⦃ prop-Q : MereProposition{ℓ}(Q) ⦄ where
  propositional-extensionalityₗ : (P ≡ Q) ← (P ↔ Q)
  propositional-extensionalityₗ pq = type-extensionalityₗ([∃]-intro pq ⦃ intro ⦄) where
    instance
      l : Inverseₗ([↔]-to-[←] pq)([↔]-to-[→] pq)
      Inverseᵣ.proof l = uniqueness(Q)

    instance
      r : Inverseᵣ([↔]-to-[←] pq)([↔]-to-[→] pq)
      Inverseᵣ.proof r = uniqueness(P)

module _ {P Q : T → Type} ⦃ prop-P : ∀{x} → MereProposition{ℓ}(P(x)) ⦄ ⦃ prop-Q : ∀{x} → MereProposition{ℓ}(Q(x)) ⦄ where
  prop-set-extensionalityₗ : (P ≡ Q) ← (∀{x} → P(x) ↔ Q(x))
  prop-set-extensionalityₗ pq = functionExtensionalityOn P Q (propositional-extensionalityₗ pq)

-- module _ ⦃ uip-P : UniqueIdentityProofs{ℓ}(P) ⦄ ⦃ uip-Q : UniqueIdentityProofs{ℓ}(Q) ⦄ where

-- TODO: Actual proof of univalence
