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
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C A₁ A₂ A₃ B₁ B₂ B₃ : Type{ℓ}

module _ where
  open import Relator.Equals using ([≡]-intro)
  open import Relator.Equals.Proofs.Equiv

  module _ ⦃ equiv-A : Equiv(A) ⦄ ⦃ equiv-B : Equiv(B) ⦄ where
    instance
      Left-injectivity : Injective(Left {A = A}{B = B})
      Injective.proof Left-injectivity [≡]-intro = [≡]-intro

    instance
      Right-injectivity : Injective(Right {A = A}{B = B})
      Injective.proof Right-injectivity [≡]-intro = [≡]-intro


module _ ⦃ equiv-C : Equiv(C) ⦄ where
  map1-values : {f : A → C}{g : B → C}{e : A ‖ B} → (∃(x ↦ map1 f g e ≡ f(x)) ∨ ∃(x ↦ map1 f g e ≡ g(x)))
  map1-values {e = Either.Left  a} = [∨]-introₗ ([∃]-intro a ⦃ reflexivity(_≡_) ⦄)
  map1-values {e = Either.Right b} = [∨]-introᵣ ([∃]-intro b ⦃ reflexivity(_≡_) ⦄)

module _ where
  module _ ⦃ _ : Equiv(A ‖ B) ⦄ where
    mapLeft-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapLeft {A = A}{B = B})(id)(id)
    _⊜_.proof (mapLeft-preserves-id) {Left  x} = reflexivity(_≡_)
    _⊜_.proof (mapLeft-preserves-id) {Right x} = reflexivity(_≡_)

    mapRight-preserves-id : Names.Preserving₀ ⦃ [⊜]-equiv ⦄ (mapRight {A = A}{B = B})(id)(id)
    _⊜_.proof (mapRight-preserves-id) {Left  x} = reflexivity(_≡_)
    _⊜_.proof (mapRight-preserves-id) {Right x} = reflexivity(_≡_)

    swap-involution : (Either.swap ∘ Either.swap {A = A}{B = B} ⊜ id)
    _⊜_.proof swap-involution {Left  _} = reflexivity(_≡_)
    _⊜_.proof swap-involution {Right _} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A₁ ; _ = A₂ ; _ = A₃ ; _ = B in Equiv(A₃ ‖ B) ⦄ {f : A₂ → A₃} {g : A₁ → A₂} where
    mapLeft-preserves-[∘] : (mapLeft(f ∘ g) ⊜ (mapLeft f) ∘ (mapLeft g))
    _⊜_.proof mapLeft-preserves-[∘] {Left  x} = reflexivity(_≡_)
    _⊜_.proof mapLeft-preserves-[∘] {Right x} = reflexivity(_≡_)

  module _ ⦃ _ : let _ = A ; _ = B₁ ; _ = B₂ ; _ = B₃ in Equiv(A ‖ B₃) ⦄ {f : B₂ → B₃} {g : B₁ → B₂} where
    mapRight-preserves-[∘] : (mapRight(f ∘ g) ⊜ (mapRight f) ∘ (mapRight g))
    _⊜_.proof mapRight-preserves-[∘] {Left  x} = reflexivity(_≡_)
    _⊜_.proof mapRight-preserves-[∘] {Right x} = reflexivity(_≡_)

  module _ ⦃ _ : Equiv(A ‖ B) ⦄ where
    map2-preserves-id : (map2 id id ⊜ id)
    _⊜_.proof map2-preserves-id {Left  x} = reflexivity(_≡_)
    _⊜_.proof map2-preserves-id {Right x} = reflexivity(_≡_)

module _ where
  open import Data.Either.Equiv
  open import Function.Equals

  module _ ⦃ _ : Equiv(A₁) ⦄ ⦃ _ : Equiv(A₂) ⦄ ⦃ _ : Equiv(B₁) ⦄ ⦃ _ : Equiv(B₂) ⦄ where
    map2-function : BinaryOperator(Either.map2 {A₁ = A₁}{A₂ = A₂}{B₁ = B₁}{B₂ = B₂})
    _⊜_.proof (BinaryOperator.congruence map2-function (intro p₁) (intro p₂)) {Left  x} = Left  p₁
    _⊜_.proof (BinaryOperator.congruence map2-function (intro p₁) (intro p₂)) {Right x} = Right p₂
