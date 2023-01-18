module Data.Either.Proofs.Map where

import      Lvl
open import Data
open import Data.Either as Either
open import Data.Either.Equiv
open import Function.Equals
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ : Lvl.Level
private variable A B C A₁ A₂ A₃ B₁ B₂ B₃ : Type{ℓ}

module _ ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ where
  map1-values : {f : A → C}{g : B → C}{e : A ‖ B} → (∃(x ↦ map1 f g e ≡ f(x)) ∨ ∃(x ↦ map1 f g e ≡ g(x)))
  map1-values {e = Either.Left  a} = [∨]-introₗ ([∃]-intro a ⦃ reflexivity(_≡_) ⦄)
  map1-values {e = Either.Right b} = [∨]-introᵣ ([∃]-intro b ⦃ reflexivity(_≡_) ⦄)

module _ where
  module _ ⦃ _ : Equiv{ℓₑ}(A ‖ B) ⦄ where
    mapLeft-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapLeft {A₁ = A}{B = B})(id)(id)
    _⊜_.proof (mapLeft-preserves-id) {Left  x} = reflexivity(_≡_)
    _⊜_.proof (mapLeft-preserves-id) {Right x} = reflexivity(_≡_)

    mapRight-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapRight {A = A}{B₁ = B})(id)(id)
    _⊜_.proof (mapRight-preserves-id) {Left  x} = reflexivity(_≡_)
    _⊜_.proof (mapRight-preserves-id) {Right x} = reflexivity(_≡_)

    swap-involution : (Either.swap ∘ Either.swap {A = A}{B = B} ⊜ id)
    _⊜_.proof swap-involution {Left  _} = reflexivity(_≡_)
    _⊜_.proof swap-involution {Right _} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A₁ ; _ = A₂ ; _ = A₃ ; _ = B in Equiv{ℓₑ}(A₃ ‖ B) ⦄ {f : A₂ → A₃} {g : A₁ → A₂} where
    mapLeft-preserves-[∘] : (mapLeft(f ∘ g) ⊜ (mapLeft f) ∘ (mapLeft g))
    _⊜_.proof mapLeft-preserves-[∘] {Left  x} = reflexivity(_≡_)
    _⊜_.proof mapLeft-preserves-[∘] {Right x} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B₁ ; _ = B₂ ; _ = B₃ in Equiv{ℓₑ}(A ‖ B₃) ⦄ {f : B₂ → B₃} {g : B₁ → B₂} where
    mapRight-preserves-[∘] : (mapRight(f ∘ g) ⊜ (mapRight f) ∘ (mapRight g))
    _⊜_.proof mapRight-preserves-[∘] {Left  x} = reflexivity(_≡_)
    _⊜_.proof mapRight-preserves-[∘] {Right x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv{ℓₑ}(A ‖ B) ⦄ where
    map-preserves-id : (map id id ⊜ id)
    _⊜_.proof map-preserves-id {Left  x} = reflexivity(_≡_)
    _⊜_.proof map-preserves-id {Right x} = reflexivity(_≡_)

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-B₁ : Equiv{ℓₑ₂}(B₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₃}(A₂) ⦄
  ⦃ equiv-B₂ : Equiv{ℓₑ₄}(B₂) ⦄
  ⦃ equiv-AB₁ : Equiv{ℓₑ₅}(A₁ ‖ B₁) ⦄ ⦃ ext-AB₁ : Extensionality(equiv-AB₁) ⦄
  ⦃ equiv-AB₂ : Equiv{ℓₑ₆}(A₂ ‖ B₂) ⦄ ⦃ ext-AB₂ : Extensionality(equiv-AB₂) ⦄
  {f : A₁ → A₂}
  {g : B₁ → B₂}
  where

  open Extensionality ⦃ … ⦄

  instance
    map-function : BinaryOperator(Either.map {A₁ = A₁}{A₂ = A₂}{B₁ = B₁}{B₂ = B₂})
    _⊜_.proof (BinaryOperator.congruence map-function (intro p₁) (intro p₂)) {Left  _} = congruence₁(Left)  p₁
    _⊜_.proof (BinaryOperator.congruence map-function (intro p₁) (intro p₂)) {Right _} = congruence₁(Right) p₂

  instance
    map-injective : ⦃ inj-f : Injective(f) ⦄ → ⦃ inj-g : Injective(g) ⦄ → Injective(Either.map f g)
    Injective.proof map-injective {Left x}  {Left  y} p = congruence₁(Either.Left)  (injective(f) (injective(Either.Left)  p))
    Injective.proof map-injective {Left x}  {Right y} p with () ← Left-Right-inequality p
    Injective.proof map-injective {Right x} {Left  y} p with () ← Left-Right-inequality (symmetry(_≡_) p)
    Injective.proof map-injective {Right x} {Right y} p = congruence₁(Either.Right) (injective(g) (injective(Either.Right) p))

  instance
    map-surjective : ⦃ surj-f : Surjective(f) ⦄ → ⦃ surj-g : Surjective(g) ⦄ → Surjective(Either.map f g)
    Surjective.proof map-surjective {Left  y} with [∃]-intro x ⦃ p ⦄ ← surjective(f){y} = [∃]-intro (Left  x) ⦃ congruence₁(Left)  p ⦄
    Surjective.proof map-surjective {Right y} with [∃]-intro x ⦃ p ⦄ ← surjective(g){y} = [∃]-intro (Right x) ⦃ congruence₁(Right) p ⦄

  instance
    map-bijective : ⦃ bij-f : Bijective(f) ⦄ → ⦃ bij-g : Bijective(g) ⦄ → Bijective(Either.map f g)
    map-bijective = injective-surjective-to-bijective(Either.map f g) where
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

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-AB : Equiv{ℓₑ}(A ‖ B) ⦄ ⦃ ext-AB : Extensionality(equiv-AB) ⦄
  where

  map-mapLeft-mapRight : ∀{f : B → A}{g : C → B} → (map f g ≡ mapLeft f ∘ mapRight g)
  _⊜_.proof (map-mapLeft-mapRight) {[∨]-introₗ _} = reflexivity(_≡_)
  _⊜_.proof (map-mapLeft-mapRight) {[∨]-introᵣ _} = reflexivity(_≡_)

  instance
    map1-function : ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ → BinaryOperator{B = (A ‖ B) → C}(map1)
    _⊜_.proof (BinaryOperator.congruence map1-function (intro p₁) (intro p₂)) {Left  _} = p₁
    _⊜_.proof (BinaryOperator.congruence map1-function (intro p₁) (intro p₂)) {Right _} = p₂
