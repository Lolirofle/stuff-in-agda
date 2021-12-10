module Structure.Operator.Monoid.Invertible.Proofs where

import      Data.Tuple as Tuple
import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Operator
open import Structure.Operator.Monoid
open import Structure.Operator.Monoid.Invertible
open import Structure.Operator.Properties hiding (InverseOperatorₗ ; InverseOperatorᵣ)
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₗ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable _▫_ : T → T → T
private variable _⨞_ : T → T → Type{ℓₗ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ monoid : Monoid{T = T}(_▫_) ⦄ ⦃ invRel : InverseRelationᵣ(_▫_){ℓₗ}(_⨞_) ⦄ where
  open Monoid(monoid) using (id)

  instance
    inverseRelationᵣ-reflexivity : Reflexivity(_⨞_)
    Reflexivity.proof inverseRelationᵣ-reflexivity = [↔]-to-[←] (InverseRelationᵣ.proof invRel) ([∃]-intro id ⦃ identityᵣ(_▫_)(id) ⦄)

  instance
    inverseRelationᵣ-transitivity : Transitivity(_⨞_)
    Transitivity.proof inverseRelationᵣ-transitivity xy yz
      with [∃]-intro a ⦃ pa ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) xy
      with [∃]-intro b ⦃ pb ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) yz
      = [↔]-to-[←] (InverseRelationᵣ.proof invRel) ([∃]-intro (a ▫ b) ⦃ symmetry(_≡_) (associativity(_▫_)) 🝖 congruence₂-₁(_▫_)(b) pa 🝖 pb ⦄)

  inverseRelationᵣ-with-opᵣ : ∀{a x y} → (x ⨞ y) → ((a ▫ x) ⨞ (a ▫ y))
  inverseRelationᵣ-with-opᵣ {a}{x}{y} xy
    with [∃]-intro z ⦃ xzy ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) xy
    = [↔]-to-[←] (InverseRelationᵣ.proof invRel) ([∃]-intro z ⦃ associativity(_▫_) 🝖 congruence₂-₂(_▫_)(a) xzy ⦄)

  inverseRelationᵣ-without-opᵣ : ⦃ cancₗ : Cancellationₗ(_▫_) ⦄ → ∀{a x y} → ((a ▫ x) ⨞ (a ▫ y)) → (x ⨞ y)
  inverseRelationᵣ-without-opᵣ {a}{x}{y} xy
    with [∃]-intro z ⦃ xzy ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) xy
    = [↔]-to-[←] (InverseRelationᵣ.proof invRel) ([∃]-intro z ⦃ cancellationₗ(_▫_) (symmetry(_≡_) (associativity(_▫_)) 🝖 xzy) ⦄)

  inverseRelationᵣ-of-idₗ : ∀{x} → (id ⨞ x)
  inverseRelationᵣ-of-idₗ {x} = [↔]-to-[←] (InverseRelationᵣ.proof invRel) ([∃]-intro x ⦃ identityₗ(_▫_)(id) ⦄)

  module _ {_⋄_ : (x : T) → (y : T) → . ⦃ inv : (y ⨞ x) ⦄ → T} ⦃ invOper : InverseOperatorᵣ(_▫_)(_⋄_) ⦄ where
    {-op-cancellationᵣ : ∀{a x y} → (a ⨞ x) → (a ⨞ y) → (a ▫ x ≡ a ▫ y) → (x ≡ y)
    op-cancellationᵣ {a}{x}{y} ax ay axay
      with [∃]-intro r ⦃ pr ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) ax
      with [∃]-intro s ⦃ ps ⦄ ← [↔]-to-[→] (InverseRelationᵣ.proof invRel) ay
      =
        x 🝖[ _≡_ ]-[ {!!} ]
        y 🝖-end-}

    inverseRelationᵣ-to-invertibleᵣ : ∀{x} → ⦃ x ⨞ id ⦄ → InvertibleElementᵣ(_▫_) ⦃ Monoid.identity-existenceᵣ(monoid) ⦄ (x)
    inverseRelationᵣ-to-invertibleᵣ {x} ⦃ xid ⦄ = [∃]-intro (id ⋄ x) ⦃ intro p ⦄ where
      p =
        (x ▫ (id ⋄ x))                                                    🝖[ _≡_ ]-[ congruence₂-₂(_▫_)(x) (InverseOperatorᵣ.proof invOper {id}{x}) ]
        (x ▫ [∃]-witness([↔]-to-[→] (InverseRelationᵣ.proof invRel) xid)) 🝖[ _≡_ ]-[ [∃]-proof([↔]-to-[→] (InverseRelationᵣ.proof invRel) xid) ]
        id                                                                🝖-end

    {- TODO: Should this not be possible without cancellation?
    inverseOperator-self : ∀{x} → let instance _ = reflexivity(_⨞_) in (x ⋄ x ≡ id)
    inverseOperator-self {x} = let instance _ = reflexivity(_⨞_) {x} in
      (x ⋄ x)                                                                        🝖[ _≡_ ]-[ InverseOperatorᵣ.proof invOper {x}{x} ]
      [∃]-witness([↔]-to-[→] (InverseRelationᵣ.proof invRel) (reflexivity(_⨞_) {x})) 🝖[ _≡_ ]-[]
      ∃.witness(Tuple.right(InverseRelationᵣ.proof invRel) (reflexivity(_⨞_)))       🝖[ _≡_ ]-[ {!!} ]
      id                                                                             🝖-end
    -}
