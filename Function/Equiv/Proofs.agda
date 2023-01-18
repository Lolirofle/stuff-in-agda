module Function.Equiv.Proofs where

open import Data
open import Functional
open import Function.Equiv
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Properties.Empty
open import Type.Properties.Inhabited
open import Type.Properties.Singleton

private variable ℓ ℓₒ ℓₘ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ : Lvl.Level
private variable T A B C : Type{ℓ}

module _
  ⦃ equiv-AC : Equiv{ℓₑ₁}(A → C) ⦄
  ⦃ equiv-BC : Equiv{ℓₑ₂}(B → C) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  ⦃ ext-AC : Extensionality equiv-C equiv-AC ⦄
  ⦃ ext-BC : Extensionality equiv-C equiv-BC ⦄
  where

  instance
    [∘]ₗ-function : ∀{g} → Function(\f → _∘_ {X = A}{Y = B}{Z = C} f g)
    Function.congruence ([∘]ₗ-function {g = g}) {f₁}{f₂} pf = functionExtensionality $ \{x} →
      f₁(g(x)) 🝖[ _≡_ ]-[ congruence₁(_$ g(x)) pf ]
      f₂(g(x)) 🝖-end

module _
  ⦃ equiv-AB : Equiv{ℓₑ₁}(A → B) ⦄
  ⦃ equiv-AC : Equiv{ℓₑ₂}(A → C) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₃}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₄}(C) ⦄
  ⦃ ext-AB : Extensionality equiv-B equiv-AB ⦄
  ⦃ ext-AC : Extensionality equiv-C equiv-AC ⦄
  ⦃ func-BC : ∀{f : B → C} → Function(f) ⦄
  where

  instance
    [∘]ᵣ-function : ∀{f} → Function(\g → _∘_ {X = A}{Y = B}{Z = C} f g)
    Function.congruence ([∘]ᵣ-function {f = f}) {g₁}{g₂} pg = functionExtensionality $ \{x} →
      f(g₁(x)) 🝖[ _≡_ ]-[ congruence₁(f) (congruence₁(_$ x) pg) ]
      f(g₂(x)) 🝖-end

module _
  ⦃ equiv-AB : Equiv{ℓₑ₁}(A → B) ⦄
  ⦃ equiv-BC : Equiv{ℓₑ₂}(B → C) ⦄
  ⦃ equiv-AC : Equiv{ℓₑ₃}(A → C) ⦄
  ⦃ equiv-A : Equiv{ℓₑ₄}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₅}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₆}(C) ⦄
  ⦃ ext-AB : Extensionality equiv-B equiv-AB ⦄
  ⦃ ext-BC : Extensionality equiv-C equiv-BC ⦄
  ⦃ ext-AC : Extensionality equiv-C equiv-AC ⦄
  ⦃ func-BC : ∀{f : B → C} → Function(f) ⦄
  where

  instance
    [∘]-binaryOperator : BinaryOperator(_∘_ {X = A}{Y = B}{Z = C})
    BinaryOperator.congruence [∘]-binaryOperator {f₁} {f₂} {g₁} {g₂} pf pg = functionExtensionality $ \{x} →
      f₁(g₁(x)) 🝖[ _≡_ ]-[ congruence₁(f₁) (congruence₁(_$ x) pg) ]
      f₁(g₂(x)) 🝖[ _≡_ ]-[ congruence₁(_$ g₂(x)) pf ]
      f₂(g₂(x)) 🝖-end

module _
  ⦃ equiv-AB : Equiv{ℓₑ₁}(A → B) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ ext : Extensionality equiv-B equiv-AB ⦄
  where

  instance
    const-function : Function(const{A = A}{B = B})
    Function.congruence const-function {c₁}{c₂} pc = functionExtensionality $ \{x} →
      const c₁ x 🝖[ _≡_ ]-[]
      c₁         🝖[ _≡_ ]-[ pc ]
      c₂         🝖[ _≡_ ]-[]
      const c₂ x 🝖-end

  instance
    const-injective : ⦃ ◊ A ⦄ → Injective(const{A = A}{B = B})
    Injective.proof const-injective = congruence₁(_$ inhabitant)

module _ ⦃ equiv-TUnit : Equiv{ℓₑ₁}(T → Unit{ℓ}) ⦄ where
  Unit-codomain-unit : IsUnit(T → Unit{ℓ})
  IsUnit.unit       Unit-codomain-unit = const <>
  IsUnit.uniqueness Unit-codomain-unit {f} = reflexivity(_≡_)

module _
  ⦃ equiv-EmptyT : Equiv{ℓₑ₁}(Empty{ℓ} → T) ⦄
  ⦃ equiv-T : Equiv{ℓₑ₂}(T) ⦄
  ⦃ ext : Extensionality equiv-T equiv-EmptyT ⦄
  where

  Empty-domain-unit : IsUnit(Empty{ℓ} → T)
  IsUnit.unit       Empty-domain-unit = Data.empty
  IsUnit.uniqueness Empty-domain-unit {f} = functionExtensionality \{}
