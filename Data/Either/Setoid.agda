module Data.Either.Setoid where

import      Lvl
open import Data.Either as Either
open import Data.Either.Equiv
open import Logic
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  data EitherEquality : (A ‖ B) → (A ‖ B) → Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂} where
    Left  : ∀{x y} → (x ≡ y) → EitherEquality(Left  x)(Left  y)
    Right : ∀{x y} → (x ≡ y) → EitherEquality(Right x)(Right y)

  EitherEquality-elim : ∀{ℓ}{P : ∀{ab₁ ab₂ : (A ‖ B)} → EitherEquality ab₁ ab₂ → Type{ℓ}} → (∀{x y : A} → (xy : (x ≡ y)) → P(Left xy)) → (∀{x y : B} → (xy : (x ≡ y)) → P(Right xy)) → ∀{ab₁ ab₂ : (A ‖ B)} → (eq : EitherEquality ab₁ ab₂) → P(eq)
  EitherEquality-elim l r (Left  p) = l p
  EitherEquality-elim l r (Right p) = r p

  EitherEquality-not-Left-Right : ∀{a : A}{b : B} → ¬(EitherEquality (Left a) (Right b))
  EitherEquality-not-Left-Right ()

  instance
    Either-equiv : Equiv(A ‖ B)
    Equiv._≡_ Either-equiv = EitherEquality
    Reflexivity.proof (Equivalence.reflexivity (Equiv.equivalence Either-equiv)) {Left  _} = Left (reflexivity(_≡_))
    Reflexivity.proof (Equivalence.reflexivity (Equiv.equivalence Either-equiv)) {Right _} = Right (reflexivity(_≡_))
    Symmetry.proof (Equivalence.symmetry (Equiv.equivalence Either-equiv)) {.(Left _)} {.(Left _)} (Left p) = Left (symmetry(_≡_) p)
    Symmetry.proof (Equivalence.symmetry (Equiv.equivalence Either-equiv)) {.(Right _)} {.(Right _)} (Right p) = Right (symmetry(_≡_) p)
    Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Either-equiv)) {.(Left _)} {.(Left _)} {.(Left _)} (Left xy) (Left yz) = Left (transitivity(_≡_) xy yz)
    Transitivity.proof (Equivalence.transitivity (Equiv.equivalence Either-equiv)) {.(Right _)} {.(Right _)} {.(Right _)} (Right xy) (Right yz) = Right (transitivity(_≡_) xy yz)

  instance
    Left-function : Function ⦃ equiv-A ⦄ ⦃ Either-equiv ⦄ (Left)
    Function.congruence Left-function = Left

  instance
    Right-function : Function ⦃ equiv-B ⦄ ⦃ Either-equiv ⦄ (Right)
    Function.congruence Right-function = Right

  instance
    Left-injectivity : Injective(Left {A = A}{B = B})
    Injective.proof Left-injectivity (Left p) = p

  instance
    Right-injectivity : Injective(Right {A = A}{B = B})
    Injective.proof Right-injectivity (Right p) = p

  instance
    EitherEquality-extensionality : Extensionality(Either-equiv)
    Extensionality.Left-Right-inequality EitherEquality-extensionality ()
