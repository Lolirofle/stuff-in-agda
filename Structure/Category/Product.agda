import      Lvl
open import Structure.Category

module Structure.Category.Product
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Structure.Setoid
open import Type

-- Statement that a category has a product object function Π of a certain index type I.
-- This means that the objects in category C have something similar to a Π-type for a specific index I.
-- Note that `proj` can be interpreted as either a projection function for a generalized tuple (product) or as a dependent function application. This is similar to the Π-type, which this is based of.
record Product {ℓ} (I : Type{ℓ}) (Π : (I → Object) → Object) : Type{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    prod : ∀{x}{f} → ((i : I) → (x ⟶ f(i))) → (x ⟶ (Π f))
    proj  : ∀{f} → (i : I) → ((Π f) ⟶ f(i))
  field
    inverse-condition : ∀{x}{f : I → Object}{i}{F : (i : I) → (x ⟶ f(i))} → (proj(i) ∘ prod(F) ≡ F(i))
    uniqueness-condition : ∀{x}{f}{g : x ⟶ (Π f)}{F : (i : I) → (x ⟶ f(i))} → (∀{i} → (proj(i) ∘ g ≡ F(i))) → (g ≡ (prod F))

  map : ∀{f}{g} → ((i : I) → (f(i) ⟶ g(i))) → ((Π f) ⟶ (Π g))
  map F = prod(\i → F(i) ∘ proj(i))
