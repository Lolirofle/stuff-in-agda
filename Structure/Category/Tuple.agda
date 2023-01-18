import      Lvl
open import Structure.Category

module Structure.Category.Tuple
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Structure.Setoid
open import Type

-- A specialization of Structure.Category.Product.
-- Also called: Cartesian product, binary products.
record Tuple(_⨯_ : Object → Object → Object) : Type{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    _<,>_  : ∀{x y z} → (x ⟶ y) → (x ⟶ z) → (x ⟶ (y ⨯ z))
    projₗ : ∀{x y} → ((x ⨯ y) ⟶ x)
    projᵣ : ∀{x y} → ((x ⨯ y) ⟶ y)
  field
    projₗ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projₗ ∘ (f <,> g) ≡ f)
    projᵣ-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z} → (projᵣ ∘ (f <,> g) ≡ g)
    uniqueness-condition : ∀{x y z}{f : x ⟶ y}{g : x ⟶ z}{h : x ⟶ (y ⨯ z)} → (projₗ ∘ h ≡ f) → (projᵣ ∘ h ≡ g) → (h ≡ (f <,> g))

  map : ∀{x₁ x₂ y₁ y₂} → (x₁ ⟶ x₂) → (y₁ ⟶ y₂) → ((x₁ ⨯ y₁) ⟶ (x₂ ⨯ y₂))
  map X Y = (X ∘ projₗ) <,> (Y ∘ projᵣ)

  swap : ∀{x y} → (x ⨯ y) ⟶ (y ⨯ x)
  swap = projᵣ <,> projₗ

  associateLeft : ∀{x y z} → ((x ⨯ y) ⨯ z) ⟵ (x ⨯ (y ⨯ z))
  associateLeft = (projₗ <,> (projₗ ∘ projᵣ)) <,> (projᵣ ∘ projᵣ)

  associateRight : ∀{x y z} → ((x ⨯ y) ⨯ z) ⟶ (x ⨯ (y ⨯ z))
  associateRight = (projₗ ∘ projₗ) <,> ((projᵣ ∘ projₗ) <,> projᵣ)

  diag : ∀{x} → x ⟶ (x ⨯ x)
  diag = id <,> id
