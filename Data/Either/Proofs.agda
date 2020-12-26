module Data.Either.Proofs where

import      Lvl
open import Data
open import Data.Either as Either
open import Function.Equals
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Categorical.Properties
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

-- TODO: Move to Data.Either.Equiv
record Correctness ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (equiv : Equiv{ℓₑ₃}(A ‖ B)) : Type{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ₃} where
  constructor intro
  private instance _ = equiv
  field
     ⦃ Left-function ⦄  : Function Left
     ⦃ Right-function ⦄ : Function Right
     ⦃ Left-injective ⦄   : Injective Left
     ⦃ Right-injective ⦄  : Injective Right
     Left-Right-inequality : ∀{x : A}{y : B} → (Left x ≢ Right y)

module _ where
  open import Relator.Equals using ([≡]-intro)
  open import Relator.Equals.Proofs.Equiv

  -- TODO: Move to Data.Either.Equiv.Id
  module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
    instance
      [≡]-Correctness : Correctness{A = A}{B = B} [≡]-equiv
      [≡]-Correctness = intro \() where
        instance
          Left-injectivity : Injective(Left)
          Injective.proof Left-injectivity [≡]-intro = [≡]-intro

        instance
          Right-injectivity : Injective(Right)
          Injective.proof Right-injectivity [≡]-intro = [≡]-intro

open Correctness ⦃ … ⦄ public

module _ ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ where
  map1-values : {f : A → C}{g : B → C}{e : A ‖ B} → (∃(x ↦ map1 f g e ≡ f(x)) ∨ ∃(x ↦ map1 f g e ≡ g(x)))
  map1-values {e = Either.Left  a} = [∨]-introₗ ([∃]-intro a ⦃ reflexivity(_≡_) ⦄)
  map1-values {e = Either.Right b} = [∨]-introᵣ ([∃]-intro b ⦃ reflexivity(_≡_) ⦄)

module _ where
  module _ ⦃ _ : Equiv{ℓₑ}(A ‖ B) ⦄ where
    mapLeft-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapLeft {A = A}{B = B})(id)(id)
    _⊜_.proof (mapLeft-preserves-id) {Left  x} = reflexivity(_≡_)
    _⊜_.proof (mapLeft-preserves-id) {Right x} = reflexivity(_≡_)

    mapRight-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapRight {A = A}{B = B})(id)(id)
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
    map2-preserves-id : (map2 id id ⊜ id)
    _⊜_.proof map2-preserves-id {Left  x} = reflexivity(_≡_)
    _⊜_.proof map2-preserves-id {Right x} = reflexivity(_≡_)

module _ where
  open import Data.Either.Setoid
  open import Function.Equals

  module _ ⦃ _ : Equiv{ℓₑ₁}(A₁) ⦄ ⦃ _ : Equiv{ℓₑ₂}(A₂) ⦄ ⦃ _ : Equiv{ℓₑ₃}(B₁) ⦄ ⦃ _ : Equiv{ℓₑ₄}(B₂) ⦄ where
    map2-function : BinaryOperator(Either.map2 {A₁ = A₁}{A₂ = A₂}{B₁ = B₁}{B₂ = B₂})
    _⊜_.proof (BinaryOperator.congruence map2-function (intro p₁) (intro p₂)) {Left  x} = Left  p₁
    _⊜_.proof (BinaryOperator.congruence map2-function (intro p₁) (intro p₂)) {Right x} = Right p₂

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-B₁ : Equiv{ℓₑ₂}(B₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₃}(A₂) ⦄
  ⦃ equiv-B₂ : Equiv{ℓₑ₄}(B₂) ⦄
  ⦃ equiv-AB₁ : Equiv{ℓₑ₅}(A₁ ‖ B₁) ⦄ ⦃ correct-AB₁ : Correctness(equiv-AB₁) ⦄
  ⦃ equiv-AB₂ : Equiv{ℓₑ₆}(A₂ ‖ B₂) ⦄ ⦃ correct-AB₂ : Correctness(equiv-AB₂) ⦄
  {f : A₁ → A₂}
  {g : B₁ → B₂}
  where

  instance
    map2-injective : ⦃ inj-f : Injective(f) ⦄ → ⦃ inj-g : Injective(g) ⦄ → Injective(Either.map2 f g)
    Injective.proof map2-injective {Left x}  {Left  y} p = congruence₁(Either.Left)  (injective(f) (injective(Either.Left)  p))
    Injective.proof map2-injective {Left x}  {Right y} p with () ← Left-Right-inequality p
    Injective.proof map2-injective {Right x} {Left  y} p with () ← Left-Right-inequality (symmetry(_≡_) p)
    Injective.proof map2-injective {Right x} {Right y} p = congruence₁(Either.Right) (injective(g) (injective(Either.Right) p))

  instance
    map2-surjective : ⦃ surj-f : Surjective(f) ⦄ → ⦃ surj-g : Surjective(g) ⦄ → Surjective(Either.map2 f g)
    Surjective.proof map2-surjective {Left  y} with [∃]-intro x ⦃ p ⦄ ← surjective(f){y} = [∃]-intro (Left  x) ⦃ congruence₁(Left)  p ⦄
    Surjective.proof map2-surjective {Right y} with [∃]-intro x ⦃ p ⦄ ← surjective(g){y} = [∃]-intro (Right x) ⦃ congruence₁(Right) p ⦄

  instance
    map2-bijective : ⦃ bij-f : Bijective(f) ⦄ → ⦃ bij-g : Bijective(g) ⦄ → Bijective(Either.map2 f g)
    map2-bijective = injective-surjective-to-bijective(Either.map2 f g) where
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
