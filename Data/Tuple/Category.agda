module Data.Tuple.Category where

open import Data.Tuple as Tuple hiding (_⨯_)
open import Data.Tuple.Equiv
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Category
import      Structure.Operator.Properties as Properties
open import Type

module _
  {ℓₒ ℓₘ}
  {Obj₁ : Type{ℓₒ}}
  {Obj₂ : Type{ℓₒ}}
  {Morphism₁ : Obj₁ → Obj₁ → Type{ℓₘ}}
  {Morphism₂ : Obj₂ → Obj₂ → Type{ℓₘ}}
  ⦃ _ : ∀{x y} → Equiv(Morphism₁ x y) ⦄
  ⦃ _ : ∀{x y} → Equiv(Morphism₂ x y) ⦄
  where

  [⨯]-obj : Type{ℓₒ}
  [⨯]-obj = Obj₁ Tuple.⨯ Obj₂

  [⨯]-morphism : [⨯]-obj → [⨯]-obj → Type{ℓₘ}
  [⨯]-morphism(x₁ , x₂) (y₁ , y₂) = (Morphism₁ x₁ y₁) Tuple.⨯ (Morphism₂ x₂ y₂)

  open Category

  _⨯_ : Category(Morphism₁) → Category(Morphism₂) → Category {Obj = [⨯]-obj} ([⨯]-morphism)
  _∘_ (cat₁ ⨯ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂} (yz₁ , yz₂) (xy₁ , xy₂) = (_∘_ cat₁ yz₁ xy₁ , _∘_ cat₂ yz₂ xy₂)
  id  (cat₁ ⨯ cat₂) {x₁ , x₂} = (id cat₁ {x₁} , id cat₂ {x₂})
  Properties.Identityₗ.proof(identityₗ(cat₁ ⨯ cat₂) {x₁ , x₂}{y₁ , y₂}) {f₁ , f₂} = [∧]-intro
    (Properties.identityₗ(_∘_ cat₁)(id cat₁) ⦃ identityₗ cat₁ {x₁}{y₁} ⦄ {f₁})
    (Properties.identityₗ(_∘_ cat₂)(id cat₂) ⦃ identityₗ cat₂ {x₂}{y₂} ⦄ {f₂})
  Properties.Identityᵣ.proof(identityᵣ(cat₁ ⨯ cat₂) {x₁ , x₂}{y₁ , y₂}) {f₁ , f₂} = [∧]-intro
    (Properties.identityᵣ(_∘_ cat₁)(id cat₁) ⦃ identityᵣ cat₁ {x₁}{y₁} ⦄ {f₁})
    (Properties.identityᵣ(_∘_ cat₂)(id cat₂) ⦃ identityᵣ cat₂ {x₂}{y₂} ⦄ {f₂})
  associativity(cat₁ ⨯ cat₂) {x₁ , x₂}{y₁ , y₂}{z₁ , z₂}{w₁ , w₂} {f₁ , f₂}{g₁ , g₂}{h₁ , h₂} = [∧]-intro
    (associativity cat₁ {x₁}{y₁}{z₁}{w₁} {f₁}{g₁}{h₁})
    (associativity cat₂ {x₂}{y₂}{z₂}{w₂} {f₂}{g₂}{h₂})
