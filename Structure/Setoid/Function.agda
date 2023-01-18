module Structure.Setoid.Function where

open import BidirectionalFunction using (_↔_ ; intro)
open import DependentFunctional using (_∘_)
open import Functional using (_on₂_)
open import Function.EqualsRaw
open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Existential
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓ₁ ℓ₂ : Lvl.Level
private variable A B C D : Setoid{ℓₑ}{ℓ}

ExtensionalFunction : Setoid{ℓₑ₁}{ℓ₁} → Setoid{ℓₑ₂}{ℓ₂} → Type
ExtensionalFunction (ⱻ A) (ⱻ B) = ∃{Obj = (A → B)} Function

instance
  ExtensionalFunction-equiv : ∀{A : Setoid{ℓₑ₁}{ℓ₁}}{B : Setoid{ℓₑ₂}{ℓ₂}} → Equiv(ExtensionalFunction A B)
  Equiv._≡_ ExtensionalFunction-equiv = (_⊜_) on₂ ◦
  Equivalence.reflexivity  (Equiv.equivalence ExtensionalFunction-equiv) = intro(\{f} → reflexivity(_⊜_) {◦ f})
  Equivalence.symmetry     (Equiv.equivalence ExtensionalFunction-equiv) = intro(symmetry(_⊜_))
  Equivalence.transitivity (Equiv.equivalence ExtensionalFunction-equiv) = intro(transitivity(_⊜_))

_→ₑₓₜ_ : Setoid{ℓₑ₁}{ℓ₁} → Setoid{ℓₑ₂}{ℓ₂} → Setoid
A →ₑₓₜ B = ⱻ(ExtensionalFunction A B)
infixr 30 _→ₑₓₜ_

_←ₑₓₜ_ : Setoid{ℓₑ₁}{ℓ₁} → Setoid{ℓₑ₂}{ℓ₂} → Setoid
A ←ₑₓₜ B = ⱻ(ExtensionalFunction B A)
infixl 30 _←ₑₓₜ_

binaryOperatorExt : (∃{Obj = (◦ A → ◦ B → ◦ C)} BinaryOperator) ↔ ◦(A →ₑₓₜ B →ₑₓₜ C)
binaryOperatorExt  = intro
  (\op → ⱻ(\a b → ◦(◦ op a) b) ⦃ BinaryOperator-unary-intro _ (intro \p → Function.congruence(⦾ op) p) (⦾(◦ op _)) ⦄)
  (\op → ⱻ(\a → ⱻ(\b → ◦ op a b) ⦃ BinaryOperator.unary₂(⦾ op) ⦄) ⦃ intro \p → BinaryOperator.congruence₁(⦾ op) _ p ⦄)

trinaryOperatorExt : (∃{Obj = (◦ A → ◦ B → ◦ C → ◦ D)} TrinaryOperator) ↔ ◦(A →ₑₓₜ B →ₑₓₜ C →ₑₓₜ D)
trinaryOperatorExt  = intro
  (\op → ⱻ(\a b c → ◦(◦(◦ op a) b) c) ⦃ TrinaryOperator-unary-intro _ (intro \p → Function.congruence(⦾ op) p) (intro \p → Function.congruence(⦾(◦ op _)) p) (⦾(◦(◦ op _) _)) ⦄)
  (\op → ⱻ(\a → ⱻ(\b → ⱻ(\c → ◦ op a b c) ⦃ TrinaryOperator.unary₃(⦾ op) ⦄) ⦃ intro \p → TrinaryOperator.congruence₂(⦾ op) _ _ p ⦄) ⦃ intro \p → TrinaryOperator.congruence₁(⦾ op) _ _ p ⦄)
