module Type.Unit.Proofs where

open import Logic
import      Lvl
open import Type.Empty
open import Type.Unit
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable A B U : Type{ℓ}

module _ ⦃ equiv : Equiv(U) ⦄ where
  instance
    unit-is-pos : ⦃ proof : IsUnit(U) ⦄ → ◊(U)
    unit-is-pos ⦃ intro unit uniqueness ⦄ = intro ⦃ unit ⦄

  instance
    unit-is-prop : ⦃ proof : IsUnit(U) ⦄ → IsProp(U)
    unit-is-prop ⦃ intro unit uniqueness ⦄ = intro (\{x}{y} → transitivity(_≡_) (uniqueness{x}) (symmetry(_≡_)(uniqueness{y})))

  instance
    pos-prop-is-unit : ⦃ _ : (◊ U) ⦄ → ⦃ _ : IsProp(U) ⦄ → IsUnit(U)
    pos-prop-is-unit ⦃ intro ⦃ unit ⦄ ⦄ ⦃ intro uniqueness ⦄ = intro unit (\{x} → uniqueness{x}{unit})

module _ ⦃ equiv-u : Equiv(U) ⦄ ⦃ is-prop : IsProp(U) ⦄ ⦃ equiv-a : Equiv(A) ⦄ where
  prop-fn-unique-value : ∀{f : U → A} → ⦃ _ : Function(f) ⦄ → (∀{x y} → (f(x) ≡ f(y)))
  prop-fn-unique-value {f = f}{x}{y} = congruence₁(f) (IsProp.uniqueness(is-prop){x}{y})

module _ ⦃ equiv-u : Equiv(U) ⦄ ⦃ is-unit : IsUnit(U) ⦄ ⦃ equiv-a : Equiv(A) ⦄ where
  unit-fn-unique-value : ∀{f : U → A} → ⦃ _ : Function(f) ⦄ → (∀{x y} → (f(x) ≡ f(y)))
  unit-fn-unique-value = prop-fn-unique-value ⦃ is-prop = unit-is-prop ⦃ proof = is-unit ⦄ ⦄

module _ ⦃ equiv-u : Equiv(U) ⦄ ⦃ is-prop : IsProp(U) ⦄ ⦃ equiv-a : Equiv(A) ⦄ where
  prop-pred-all : ∀{f : U → A} → ⦃ _ : Function(f) ⦄ → (∀{x y} → (f(x) ≡ f(y)))
  prop-pred-all {f = f}{x}{y} = congruence₁(f) (IsProp.uniqueness(is-prop){x}{y})

{- TODO
-- Any binary relation on Unit is an equivalence given that it is reflexive.
module _ ⦃ equiv-u : Equiv(U) ⦄ ⦃ is-unit : IsUnit(U) ⦄ {_▫_ : U → U → Stmt} where
  unit-equiv : Equiv(U)
  Equiv._≡_ unit-equiv = (_▫_)
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence unit-equiv))       = {!!}
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence unit-equiv)) _     = {!!}
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence unit-equiv)) _ _   = {!!}
-}
