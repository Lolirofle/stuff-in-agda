module Data.Tuple.Equivalence where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    Tuple-equiv : Equiv(A ⨯ B)
    _≡_ ⦃ Tuple-equiv ⦄ (x₁ , y₁) (x₂ , y₂) = (x₁ ≡ x₂) ∧ (y₁ ≡ y₂)
    Equiv-equivalence ⦃ Tuple-equiv ⦄ = intro where
      instance
        [≡]-reflexivity : Reflexivity(_≡_ ⦃ Tuple-equiv ⦄)
        Reflexivity.proof([≡]-reflexivity) = [∧]-intro (reflexivity(_≡_)) (reflexivity(_≡_))

      instance
        [≡]-symmetry : Symmetry(_≡_ ⦃ Tuple-equiv ⦄)
        Symmetry.proof([≡]-symmetry) ([∧]-intro l r) = [∧]-intro (symmetry(_≡_) l) (symmetry(_≡_) r)

      instance
        [≡]-transitivity : Transitivity(_≡_ ⦃ Tuple-equiv ⦄)
        Transitivity.proof([≡]-transitivity) ([∧]-intro l1 r1) ([∧]-intro l2 r2) = [∧]-intro (transitivity(_≡_) l1 l2) (transitivity(_≡_) r1 r2)

  instance
    left-function : Function(Tuple.left)
    Function.congruence left-function = Tuple.left

  instance
    right-function : Function(Tuple.right)
    Function.congruence right-function = Tuple.right

  instance
    [,]-function : BinaryOperator(_,_)
    BinaryOperator.congruence [,]-function a b = (a , b)

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  instance
    swap-function : Function ⦃ Tuple-equiv ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦄ ⦃ Tuple-equiv ⦄ (Tuple.swap)
    Function.congruence swap-function = Tuple.swap

module _ {A : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(A) ⦄ where
  instance
    repeat-function : Function(Tuple.repeat{A = A})
    Function.congruence repeat-function = Tuple.repeat

module _
  {A₁ : Type{ℓₒ₁}} ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  {A₂ : Type{ℓₒ₂}} ⦃ equiv-A₂ : Equiv{ℓₑ₂}(A₂) ⦄
  {B₁ : Type{ℓₒ₃}} ⦃ equiv-B₁ : Equiv{ℓₑ₃}(B₁) ⦄
  {B₂ : Type{ℓₒ₄}} ⦃ equiv-B₂ : Equiv{ℓₑ₄}(B₂) ⦄
  {f : A₁ → A₂} ⦃ func-f : Function(f) ⦄
  {g : B₁ → B₂} ⦃ func-g : Function(g) ⦄
  where

  instance
    map-function : Function(Tuple.map f g)
    Function.congruence map-function = Tuple.map (congruence₁(f)) (congruence₁(g))

module _
  {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {C : Type{ℓₒ₃}} ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  where

  instance
    associateLeft-function : Function(Tuple.associateLeft {A = A}{B = B}{C = C})
    Function.congruence associateLeft-function = Tuple.associateLeft

  instance
    associateRight-function : Function(Tuple.associateRight {A = A}{B = B}{C = C})
    Function.congruence associateRight-function = Tuple.associateRight
