module Structure.Type.Function.Functions where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
import      Function as Fn
import      Lvl
open import Type
open import Structure.Setoid
open import Structure.Type.Function
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ where
  private variable _⟶_ _⟶₁_ _⟶₂_ _⟶₃_ _⟶₄_ : Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₃}
  private variable ⦃ equiv equiv₁ equiv₂ equiv₃ equiv₄ ⦄ : ∀{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₑ}(A ⟶ B)

  id : ⦃ fn : FunctionType(_⟶_) ⦃ \{A}{B} → equiv{A}{B} ⦄ ⦄ → (A ⟶ A)
  id = lift Fn.id

  map :
    ⦃ fn₁ : FunctionType(_⟶₁_) ⦃ \{A}{B} → equiv₁{A}{B} ⦄ ⦄ →
    ⦃ fn₂ : FunctionType(_⟶₂_) ⦃ \{A}{B} → equiv₂{A}{B} ⦄ ⦄ →
    (A ⟶₁ B) →
    (A ⟶₂ B)
  map f = lift(f $_)

  _∘ₛ_ :
    ⦃ fn₁ : FunctionType(_⟶₁_) ⦃ \{A}{B} → equiv₁{A}{B} ⦄ ⦄ →
    ⦃ fn₂ : FunctionType(_⟶₂_) ⦃ \{A}{B} → equiv₂{A}{B} ⦄ ⦄ →
    ⦃ fn₃ : FunctionType(_⟶₃_) ⦃ \{A}{B} → equiv₃{A}{B} ⦄ ⦄ →
    (A ⟶₂ (B ⟶₃ C)) →
    (A ⟶₁ B) →
    ⦃ fn₄ : FunctionType(_⟶₄_) ⦃ \{A}{B} → equiv₄{A}{B} ⦄ ⦄ →
    (A ⟶₄ C)
  f ∘ₛ g = lift(x ↦ (f $ x) $ (g $ x))

  _∘_ :
    ⦃ fn₁ : FunctionType(_⟶₁_) ⦃ \{A}{B} → equiv₁{A}{B} ⦄ ⦄ →
    ⦃ fn₂ : FunctionType(_⟶₂_) ⦃ \{A}{B} → equiv₂{A}{B} ⦄ ⦄ →
    (B ⟶₂ C) →
    (A ⟶₁ B) →
    ⦃ fn₃ : FunctionType(_⟶₃_) ⦃ \{A}{B} → equiv₃{A}{B} ⦄ ⦄ →
    (A ⟶₃ C)
  f ∘ g = lift(x ↦ f $ (g $ x))
