module Type.Properties.Singleton.Proofs where

import      Data.Tuple as Tuple
open import Data.Proofs
open import Function.Axioms
open import Logic.Classical
open import Logic
import      Lvl
open import Type.Properties.Empty
open import Type.Properties.Inhabited
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Syntax.Function
open import Type.Dependent
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ : Lvl.Level
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

module _
  ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-b : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₃}(A ∧ B) ⦄
  ⦃ op : BinaryOperator([∧]-intro) ⦄ where
  instance
    prop-conjunction : ⦃ prop-a : MereProposition(A) ⦄ ⦃ prop-b : MereProposition(B) ⦄ → MereProposition(A ∧ B)
    MereProposition.uniqueness prop-conjunction {[∧]-intro a₁ b₁} {[∧]-intro a₂ b₂} = congruence₂([∧]-intro) (uniqueness(A)) (uniqueness(B))

module _
  ⦃ equiv-b : Equiv{ℓₑ₁}(B) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₂}(A → B) ⦄
  ⦃ funcExt : FunctionExtensionality(A)(B) ⦄
  where
  prop-implication : ⦃ prop-b : MereProposition(B) ⦄ → MereProposition(A → B)
  MereProposition.uniqueness prop-implication = functionExtensionality(A)(B) (uniqueness(B))

module _
  {B : A → Type{ℓ}}
  ⦃ equiv-b : ∀{a} → Equiv{ℓₑ₁}(B(a)) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₂}((a : A) → B(a)) ⦄
  ⦃ funcExt : DependentFunctionExtensionality(A)(B) ⦄
  where
  prop-dependent-implication : ⦃ prop-b : ∀{a} → MereProposition(B(a)) ⦄ → MereProposition((a : A) → B(a))
  MereProposition.uniqueness prop-dependent-implication = dependentFunctionExtensionality(A)(B)(\{a} → uniqueness(B(a)))

module _ ⦃ equiv-top : Equiv{ℓₑ}(⊤) ⦄ where
  instance
    prop-top : MereProposition(⊤)
    prop-top = unit-is-prop

module _ ⦃ equiv-bottom : Equiv{ℓₑ}(⊥) ⦄ where
  instance
    prop-bottom : MereProposition(⊥) ⦃ equiv-bottom ⦄
    MereProposition.uniqueness prop-bottom {}

module _
  {P : A → Type{ℓ}} ⦃ equiv-p : ∀{x} → Equiv{ℓₑ₁}(P(x)) ⦄
  ⦃ equiv-ap : Equiv{ℓₑ₂}(∀ₗ P) ⦄
  ⦃ funcExt : DependentImplicitFunctionExtensionality(A)(P) ⦄
  where
  prop-universal : ⦃ prop-p : ∀{x} → MereProposition(P(x)) ⦄ → MereProposition(∀ₗ P)
  MereProposition.uniqueness prop-universal = dependentImplicitFunctionExtensionality(A)(P) (\{x} → uniqueness(P(x)))

module _
  ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-b : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-ba : Equiv{ℓₑ₃}(A ← B) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₄}(A → B) ⦄
  ⦃ equiv-eq : Equiv{ℓₑ₅}(A ↔ B) ⦄
  ⦃ op : BinaryOperator([↔]-intro) ⦄
  ⦃ funcExtₗ : FunctionExtensionality(B)(A) ⦄
  ⦃ funcExtᵣ : FunctionExtensionality(A)(B) ⦄
  where
  prop-equivalence : ⦃ prop-a : MereProposition(A) ⦄ → ⦃ prop-b : MereProposition(B) ⦄ → MereProposition(A ↔ B)
  prop-equivalence = prop-conjunction ⦃ prop-a = prop-implication ⦄ ⦃ prop-b = prop-implication ⦄

module _
  ⦃ equiv-na : Equiv{ℓₑ}(¬ A) ⦄
  ⦃ funcExt : FunctionExtensionality(A)(⊥) ⦄
  where
  prop-negation : MereProposition(¬ A)
  prop-negation = prop-implication

module _
  ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-b : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₃}(A ∨ B) ⦄
  (left-right-neq : ∀{a : A}{b : B} → ([∨]-introₗ a ≢ [∨]-introᵣ b))
  where
  not-prop-disjunction : MereProposition(A ∨ B) → IsEmpty(A ∧ B)
  IsEmpty.empty (not-prop-disjunction (intro uniqueness)) ([∧]-intro a b) with () ← left-right-neq(uniqueness{[∨]-introₗ a}{[∨]-introᵣ b})

{- TODO
module _
  ⦃ equiv-a : Equiv(A) ⦄
  {B : A → Type{ℓ}} ⦃ equiv-b : ∀{x} → Equiv(B(x)) ⦄
  ⦃ equiv-sigma : Equiv(Σ A B) ⦄ -- TODO: Not an arbitrary one
  where
  prop-sigma : MereProposition(Σ A B) → ? -- TODO: Maybe MereProposition(B) → MereProposition(A)
  prop-sigma (intro uniqueness₁) = {!!}
-}

{- TODO: Maybe generalize and move the stuff from Data.Proofs to here
-- Any binary relation on Unit is an equivalence given that it is reflexive.
module _ ⦃ equiv-u : Equiv(U) ⦄ ⦃ is-unit : IsUnit(U) ⦄ {_▫_ : U → U → Stmt} where
  unit-equiv : Equiv(U)
  Equiv._≡_ unit-equiv = (_▫_)
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence unit-equiv))       = {!!}
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence unit-equiv)) _     = {!!}
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence unit-equiv)) _ _   = {!!}
-}
