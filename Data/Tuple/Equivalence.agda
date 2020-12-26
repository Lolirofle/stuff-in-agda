module Data.Tuple.Equivalence where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional
open import Structure.Setoid.WithLvl
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
    repeat-function : Function(Tuple.repeat{X = A})
    Function.congruence repeat-function = Tuple.repeat

module _
  {X₁ : Type{ℓₒ₁}} ⦃ equiv-X₁ : Equiv{ℓₑ₁}(X₁) ⦄
  {X₂ : Type{ℓₒ₂}} ⦃ equiv-X₂ : Equiv{ℓₑ₂}(X₂) ⦄
  {Y₁ : Type{ℓₒ₃}} ⦃ equiv-Y₁ : Equiv{ℓₑ₃}(Y₁) ⦄
  {Y₂ : Type{ℓₒ₄}} ⦃ equiv-Y₂ : Equiv{ℓₑ₄}(Y₂) ⦄
  {f : X₁ → X₂}
  ⦃ func-f : Function(f) ⦄
  {g : Y₁ → Y₂}
  ⦃ func-g : Function(g) ⦄
  where

  instance
    map-function : Function(Tuple.map f g)
    Function.congruence map-function = Tuple.map (congruence₁(f)) (congruence₁(g))

module _
  {X : Type{ℓₒ₁}} ⦃ equiv-X : Equiv{ℓₑ₁}(X) ⦄
  {Y : Type{ℓₒ₂}} ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄
  {Z : Type{ℓₒ₃}} ⦃ equiv-Z : Equiv{ℓₑ₃}(Z) ⦄
  where

  instance
    associateLeft-function : Function(Tuple.associateLeft {X = X}{Y = Y}{Z = Z})
    Function.congruence associateLeft-function = Tuple.associateLeft

  instance
    associateRight-function : Function(Tuple.associateRight {X = X}{Y = Y}{Z = Z})
    Function.congruence associateRight-function = Tuple.associateRight
