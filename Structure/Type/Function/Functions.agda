module Structure.Type.Function.Functions where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
import      Function as Fn
import      Lvl
open import Type
open import Structure.Setoid
open import Structure.Type.Function
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₑ ℓₒ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable _⟶_ _⟶₁_ _⟶₂_ _⟶₃_ _⟶₄_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}

id : ⦃ fn : FunctionType(_⟶_) ⦄ → (A ⟶ A)
id = abstr Fn.id

map :
  ⦃ fn₁ : FunctionType(_⟶₁_) ⦄ →
  ⦃ fn₂ : FunctionType(_⟶₂_) ⦄ →
  (A ⟶₁ B) →
  (A ⟶₂ B)
map f = abstr(f $_)

_∘ₛ_ :
  ⦃ fn₁ : FunctionType(_⟶₁_) ⦄ →
  ⦃ fn₂ : FunctionType(_⟶₂_) ⦄ →
  ⦃ fn₃ : FunctionType(_⟶₃_) ⦄ →
  (A ⟶₂ (B ⟶₃ C)) →
  (A ⟶₁ B) →
  ⦃ fn₄ : FunctionType(_⟶₄_) ⦄ →
  (A ⟶₄ C)
f ∘ₛ g = abstr(x ↦ (f $ x) $ (g $ x))

_∘_ :
  ⦃ fn₁ : FunctionType(_⟶₁_) ⦄ →
  ⦃ fn₂ : FunctionType(_⟶₂_) ⦄ →
  (B ⟶₂ C) →
  (A ⟶₁ B) →
  ⦃ fn₃ : FunctionType(_⟶₃_) ⦄ →
  (A ⟶₃ C)
f ∘ g = abstr(x ↦ f $ (g $ x))
