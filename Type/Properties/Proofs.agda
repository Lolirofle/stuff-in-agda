module Type.Properties.Proofs where

open import Data as Data using (Empty)
open import Logic.Propositional
import      Lvl
open import Type.Properties.Empty
open import Type.Properties.Inhabited
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Structure.Setoid
open import Structure.Function
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓₜ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ : Lvl.Level
private variable A B T U P : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(U) ⦄ where
  unit-is-pos : ⦃ proof : IsUnit(U) ⦄ → ◊(U)
  unit-is-pos ⦃ intro unit uniqueness ⦄ = intro ⦃ unit ⦄

  unit-is-prop : ⦃ proof : IsUnit(U) ⦄ → MereProposition(U)
  unit-is-prop ⦃ intro unit uniqueness ⦄ = intro (\{x}{y} → transitivity(_≡_) (uniqueness{x}) (symmetry(_≡_)(uniqueness{y})))

  pos-prop-is-unit : ⦃ _ : (◊ U) ⦄ → ⦃ _ : MereProposition(U) ⦄ → IsUnit(U)
  pos-prop-is-unit ⦃ intro ⦃ unit ⦄ ⦄ ⦃ intro uniqueness ⦄ = intro unit (\{x} → uniqueness{x}{unit})

module _ ⦃ equiv-p : Equiv{ℓₑ}(P) ⦄ ⦃ prop-p : MereProposition(P) ⦄ ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄ where
  prop-fn-unique-value : ∀{f : P → A} → ⦃ _ : Function(f) ⦄ → (∀{x y} → (f(x) ≡ f(y)))
  prop-fn-unique-value {f = f}{x}{y} = congruence₁(f) (MereProposition.uniqueness(prop-p){x}{y})

module _ ⦃ equiv-u : Equiv{ℓₑ}(U) ⦄ ⦃ unit-u : IsUnit(U) ⦄ ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄ where
  unit-fn-unique-value : ∀{f : U → A} → ⦃ _ : Function(f) ⦄ → (∀{x y} → (f(x) ≡ f(y)))
  unit-fn-unique-value = prop-fn-unique-value ⦃ prop-p = unit-is-prop ⦃ proof = unit-u ⦄ ⦄

-- A type is never inhabited and empty at the same time.
notInhabitedAndEmpty : (◊ T) → IsEmpty{ℓₜ}(T) → ⊥
notInhabitedAndEmpty i e = Data.empty(empty ⦃ e ⦄ (inhabitant ⦃ i ⦄))
