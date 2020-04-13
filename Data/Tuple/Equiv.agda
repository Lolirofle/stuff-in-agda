module Data.Tuple.Equiv where

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

private variable ℓₒ₁ ℓₒ₂ : Lvl.Level

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ where
  instance
    Tuple-equiv : Equiv(A ⨯ B)
    _≡_ ⦃ Tuple-equiv ⦄ (x₁ , y₁) (x₂ , y₂) = (x₁ ≡ x₂) ∧ (y₁ ≡ y₂)
    [≡]-equivalence ⦃ Tuple-equiv ⦄ = intro where
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

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv(B) ⦄ where
  instance
    swap-function : Function ⦃ Tuple-equiv ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦄ ⦃ Tuple-equiv ⦄ (Tuple.swap)
    Function.congruence swap-function = Tuple.swap
