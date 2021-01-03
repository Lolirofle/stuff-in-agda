module Data.Tuple.Proofs where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv
open import Function.Equals
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ : Lvl.Level
private variable A B A₁ B₁ A₂ B₂ : Type{ℓ}
private variable f g : A → B
private variable p : A ⨯ B

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-AB : Equiv{ℓₑ}(A ⨯ B) ⦄ ⦃ ext-AB : Extensionality(equiv-AB) ⦄
  where
  open Extensionality(ext-AB)

  [,]-left-right-inverses : ∀{x : A ⨯ B} → ((Tuple.left x , Tuple.right x) ≡ x)
  [,]-left-right-inverses {_ , _} = reflexivity(_≡_)

  left-right-[,]-inverses : ∀{a : A}{b : B} → ((Tuple.left(a , b) ≡ a) ∧ (Tuple.right(a , b) ≡ b))
  left-right-[,]-inverses = [∧]-intro (reflexivity(_≡_)) (reflexivity(_≡_))

  instance
    [,]ₗ-injective : ∀{r : B} → Injective(_, r)
    Injective.proof [,]ₗ-injective = congruence₁(Tuple.left)

  instance
    [,]ᵣ-injective : ∀{l : A} → Injective(l ,_)
    Injective.proof [,]ᵣ-injective = congruence₁(Tuple.right)

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-B₁ : Equiv{ℓₑ₂}(B₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₃}(A₂) ⦄
  ⦃ equiv-B₂ : Equiv{ℓₑ₄}(B₂) ⦄
  ⦃ equiv-AB₁ : Equiv{ℓₑ₅}(A₁ ⨯ B₁) ⦄ ⦃ equiv-AB₁ : Extensionality(equiv-AB₁) ⦄
  ⦃ equiv-AB₂ : Equiv{ℓₑ₆}(A₂ ⨯ B₂) ⦄ ⦃ equiv-AB₂ : Extensionality(equiv-AB₂) ⦄
  {f : A₁ → A₂}
  {g : B₁ → B₂}
  where

  instance
    map-function : BinaryOperator(Tuple.map {A₁ = A₁}{A₂ = A₂}{B₁ = B₁}{B₂ = B₂})
    _⊜_.proof (BinaryOperator.congruence map-function (intro eq₁) (intro eq₂)) {_ , _} = congruence₂(_,_) eq₁ eq₂

  instance
    map-injective : ⦃ inj-f : Injective(f) ⦄ → ⦃ inj-g : Injective(g) ⦄ → Injective(Tuple.map f g)
    Injective.proof map-injective {_ , _} {_ , _} p = congruence₂(_,_) (injective(f) (congruence₁(Tuple.left) p)) (injective(g) (congruence₁(Tuple.right) p))

  instance
    map-surjective : ⦃ surj-f : Surjective(f) ⦄ → ⦃ surj-g : Surjective(g) ⦄ → Surjective(Tuple.map f g)
    ∃.witness (Surjective.proof map-surjective {l , r}) = ([∃]-witness(surjective(f) {l}) , [∃]-witness(surjective(g) {r}))
    ∃.proof   (Surjective.proof map-surjective {l , r}) = congruence₂(_,_) ([∃]-proof(surjective(f) {l})) ([∃]-proof(surjective(g) {r}))

  instance
    map-bijective : ⦃ bij-f : Bijective(f) ⦄ → ⦃ bij-g : Bijective(g) ⦄ → Bijective(Tuple.map f g)
    map-bijective = injective-surjective-to-bijective(Tuple.map f g) where
      instance
        inj-f : Injective(f)
        inj-f = bijective-to-injective(f)
      instance
        inj-g : Injective(g)
        inj-g = bijective-to-injective(g)
      instance
        surj-f : Surjective(f)
        surj-f = bijective-to-surjective(f)
      instance
        surj-g : Surjective(g)
        surj-g = bijective-to-surjective(g)
