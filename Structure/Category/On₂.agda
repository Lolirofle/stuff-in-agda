module Structure.Category.On₂ where

open import Logic.Propositional
import      Lvl
open import Structure.Category
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Setoid.On₂
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}

-- Constructs the category on the left-hand side of a functor when given the right-hand side.
module _
  {_⟶₁_ : A → A → Type{ℓ₁}}
  ⦃ equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶₁ y) ⦄
  ⦃ C : Category(_⟶₁_) ⦃ equiv ⦄ ⦄

  {_⟶₂_ : B → B → Type{ℓ₂}}
  (_∘₂_ : ∀{x y z} → (y ⟶₂ z) → (x ⟶₂ y) → (x ⟶₂ z))
  (id₂ : ∀{x} → (x ⟶₂ x))

  (F : B → A)
  (map : ∀{x y} → (x ⟶₂ y) → (F(x) ⟶₁ F(y)))
  ⦃ map-func : ∀{x y} → Function ⦃ on₂-equiv map ⦃ equiv ⦄ ⦄ ⦃ equiv ⦄ (map{x}{y}) ⦄
  where

  private open module MorphismEquiv{x}{y} = Equiv(equiv{x}{y}) using ()
  open Category(C) using () renaming (_∘_ to _∘₁_ ; id to id₁ ; identityₗ to identityₗ₁ ; identityᵣ to identityᵣ₁)

  module _
    ⦃ preserves-[∘] : ∀{x y z} → Preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_ {x = x}{y = y}{z = z}) (_∘₁_) ⦄
    ⦃ preserves-id : ∀{x} → Preserving₀(_⟶₂_)(_⟶₁_) map (id₂{x = x}) id₁ ⦄
    where

    on₂-category : Category(_⟶₂_) ⦃ on₂-equiv map ⦃ equiv ⦄ ⦄
    Category._∘_ on₂-category = _∘₂_
    Category.id  on₂-category = id₂
    Category.binaryOperator on₂-category = intro \{x₁}{y₁}{x₂}{y₂} p₁ p₂ →
      map(x₁ ∘₂ x₂)      🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]
      map(x₁) ∘₁ map(x₂) 🝖[ _≡_ ]-[ congruence₂(_∘₁_) p₁ p₂ ]
      map(y₁) ∘₁ map(y₂) 🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]-sym
      map(y₁ ∘₂ y₂)      🝖[ _≡_ ]-end
    Category.associativity on₂-category = Morphism.intro \{a}{b}{c}{d} {F}{G}{H} →
      map((F ∘₂ G) ∘₂ H)           🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]
      map(F ∘₂ G) ∘₁ map(H)        🝖[ _≡_ ]-[ congruence₂-₁(_∘₁_)(map(H)) (preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_)) ]
      (map(F) ∘₁ map(G)) ∘₁ map(H) 🝖[ _≡_ ]-[ Morphism.associativity(_∘₁_) ]
      map(F) ∘₁ (map(G) ∘₁ map(H)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘₁_)(map(F)) (preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_)) ]-sym
      map(F) ∘₁ map(G ∘₂ H)        🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]-sym
      map(F ∘₂ (G ∘₂ H))           🝖-end
    Category.identity on₂-category = [∧]-intro
      (Morphism.intro \{x}{y} {F} →
        map(id₂ ∘₂ F)      🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]
        map(id₂) ∘₁ map(F) 🝖[ _≡_ ]-[ congruence₂-₁(_∘₁_)(map(F)) (preserving₀(_⟶₂_)(_⟶₁_) map id₂ id₁) ]
        id₁ ∘₁ map(F)      🝖[ _≡_ ]-[ Morphism.identityₗ(_∘₁_)(id₁) ]
        map(F)             🝖-end
      )
      (Morphism.intro \{x}{y} {F} →
        map(F ∘₂ id₂)      🝖[ _≡_ ]-[ preserving₂(_⟶₂_)(_⟶₁_) map (_∘₂_)(_∘₁_) ]
        map(F) ∘₁ map(id₂) 🝖[ _≡_ ]-[ congruence₂-₂(_∘₁_)(map(F)) (preserving₀(_⟶₂_)(_⟶₁_) map id₂ id₁) ]
        map(F) ∘₁ id₁      🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘₁_)(id₁) ]
        map(F)             🝖-end
      )
