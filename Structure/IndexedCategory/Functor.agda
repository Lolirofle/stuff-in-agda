import      Lvl
open import Type

module Structure.IndexedCategory.Functor where

open import Structure.IndexedCategory as IndexedCategory
open import Structure.IndexedOperator.Properties
open import Structure.IndexedRelator.Properties
open import Structure.Setoid

private variable ℓᵢ : Lvl.Level
private variable I I₁ I₂ : Type{ℓᵢ}
private variable ℓₒ : I → Lvl.Level
private variable ℓₘ ℓₑ : I → I → Lvl.Level
private variable Obj Obj₁ Obj₂ : (i : I) → Type{ℓₒ i}
private variable _⟶_ _⟶₁_ _⟶₂_ : ∀{i₁ i₂} → Obj(i₁) → Obj(i₂) → Type{ℓₘ i₁ i₂}
{-private variable ⦃ morphism-equiv ⦄ ⦃ morphism-equiv₁ ⦄ ⦃ morphism-equiv₂ ⦄ : ∀{i₁ i₂ : I}{x : Obj(i₁)}{y : Obj(i₂)} → Equiv{ℓₑ i₁ i₂}{ℓₘ i₁ i₂}(x ⟶ y)

private variable _∘_ _∘₁_ _∘₂_ : Names.FlippedTransitivity {ℓᵢ} I {ℓₒ}{ℓₘ} (Obj)(_⟶_)
private variable id id₁ id₂ : Names.Reflexivity I {ℓₒ}{ℓₘ} (Obj)(_⟶_)

module _ where
  record Functor(C₁ : IndexedCategory.Properties I₁ Obj₁ (_⟶₁_) ⦃ morphism-equiv₁ ⦄ (_∘₁_) id₁) (C₂ : IndexedCategory.Properties I₂ Obj₂ (_⟶₂_) ⦃ morphism-equiv₂ ⦄ (_∘₂_) id₂) : Typeω where
    field
      index  : I₁ → I₂
      object : ∀{i} → Obj₁(i) → Obj₂(index(i))
      map    : ∀{i₁ i₂}{A : Obj₁(i₁)}{B : Obj₁(i₂)} → (A ⟶₁ B) → (object(A) ⟶₂ object(B))
-}
