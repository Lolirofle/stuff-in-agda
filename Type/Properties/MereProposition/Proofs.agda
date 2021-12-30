module Type.Properties.MereProposition.Proofs where

open import Data.Proofs
open import Function.Axioms
import      Lvl
open import Type.Properties.Empty
open import Type.Properties.MereProposition
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Operator
open import Type.Properties.Proofs
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ : Lvl.Level
private variable A B T U P : Type{ℓ}

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
    prop-top : MereProposition(⊤) ⦃ equiv-top ⦄
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
  ⦃ equiv-a      : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-bottom : Equiv{ℓₑ₂}(⊥) ⦄
  ⦃ equiv-na     : Equiv{ℓₑ₃}(¬ A) ⦄
  ⦃ funcExt : FunctionExtensionality (A)(⊥) ⦃ equiv-bottom ⦄ ⦄
  where
  prop-negation : MereProposition(¬ A)
  prop-negation = prop-implication

module _
  ⦃ equiv-a : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-b : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-ab : Equiv{ℓₑ₃}(A ∨ B) ⦄
  (left-right-neq : ∀{a : A}{b : B} → ([∨]-introₗ a ≢ [∨]-introᵣ b))
  where
  not-prop-disjunction : MereProposition(A ∨ B) → IsEmpty{ℓ}(A ∧ B)
  IsEmpty.empty (not-prop-disjunction (intro uniqueness)) ([∧]-intro a b) with () ← left-right-neq(uniqueness{[∨]-introₗ a}{[∨]-introᵣ b})

{-
module _ {B : A → Type{ℓ}} where
  open import Type.Identity
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Relator
  open import Structure.Setoid.Uniqueness
  open import Syntax.Transitivity

  congruence₁-dependent : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : A → Type{ℓ₂}}{a₁ a₂ : A} → (f : (a : A) → B(a)) → (pa : a₁ ≡ a₂) → (substitute₁ᵣ(B) pa (f a₁) ≡ f a₂)
  congruence₁-dependent _ intro = intro

  -- congruence₂-dependent : ∀{C : (a : A) → B(a) → Type{ℓ}}{a₁ a₂ : A}{b₁ : B(a₁)}{b₂ : B(a₂)}{f : (a : A) → (b : B(a)) → C a b} → (pa : a₁ ≡ a₂) → (f a₁ b₁ ≡ f a₂ b₂)
  -- (substitute₁ᵣ(B) ? b₁)

  prop-sigma : Unique(B) → (∀{a} → MereProposition(B(a))) → MereProposition(Σ A B)
  MereProposition.uniqueness (prop-sigma unique-B prop-B) {intro xa xb} {intro ya yb} =
    intro xa xb                                   🝖[ _≡_ ]-[ {!(congruence₁-dependent(intro) (unique-B xb yb))!} ]
    intro ya (substitute₁ᵣ(B) (unique-B xb yb) xb) 🝖[ _≡_ ]-[ {!intro xa xb!} ]
    intro ya yb                                   🝖-end
-}

{- TODO
module _
  ⦃ equiv-a : Equiv(A) ⦄
  {B : A → Type{ℓ}} ⦃ equiv-b : ∀{x} → Equiv(B(x)) ⦄
  ⦃ equiv-sigma : Equiv(Σ A B) ⦄ -- TODO: Not an arbitrary one
  where
  prop-sigma : MereProposition(Σ A B) → ? -- TODO: Maybe MereProposition(B) → MereProposition(A)
  prop-sigma (intro uniqueness₁) = {!!}
-}
