module Structure.Category.Slice where

import      Lvl
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Logic.Propositional
open import Structure.Category
open import Structure.Category.Dual
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Dependent.Sigma

private variable ℓ ℓₒ ℓₘ ℓₑ : Lvl.Level
private variable Obj : Type{ℓₒ}
private variable _⟶_ : Obj → Obj → Type{ℓₘ}

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(x ⟶ y) ⦄
  (C : Category(_⟶_))
  (c : Obj)
  where

  open Category(C)
  private open module MorphismEquiv {x}{y} = Equiv(morphism-equiv{x}{y}) hiding (_≡_)

  OverObject : Type
  OverObject = Σ Obj (_⟶ c)

  OverMorphism : OverObject → OverObject → Type
  OverMorphism (intro x f) (intro y g) = ∃(\h → g ∘ h ≡ f)

  _∘ₒᵥₑᵣ_ : ∀{x y z} → OverMorphism y z → OverMorphism x y → OverMorphism x z
  _∘ₒᵥₑᵣ_ {intro x px} {intro y py} {intro z pz} ([∃]-intro f ⦃ pf ⦄) ([∃]-intro g ⦃ pg ⦄) = [∃]-intro (f ∘ g) ⦃ p ⦄ where
    p =
      pz ∘ (f ∘ g) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
      (pz ∘ f) ∘ g 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(g) pf ]
      py ∘ g       🝖[ _≡_ ]-[ pg ]
      px           🝖-end

  idₒᵥₑᵣ : ∀{x} → OverMorphism x x
  idₒᵥₑᵣ = [∃]-intro id ⦃ Morphism.identityᵣ(_∘_)(id) ⦄

  -- Also called: Slice category, over category.
  overCategory : Category(OverMorphism)
  Category._∘_ overCategory = _∘ₒᵥₑᵣ_
  Category.id  overCategory = idₒᵥₑᵣ
  Category.binaryOperator overCategory = intro(congruence₂(_∘_))
  Category.associativity  overCategory = Morphism.intro(Morphism.associativity(_∘_))
  Category.identity       overCategory = [∧]-intro (Morphism.intro (Morphism.identityₗ(_∘_)(id))) (Morphism.intro (Morphism.identityᵣ(_∘_)(id)))

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(x ⟶ y) ⦄
  (C : Category(_⟶_))
  (c : Obj)
  where

  UnderObject : Type
  UnderObject = OverObject(dualCategory(C))(c)

  UnderMorphism : UnderObject → UnderObject → Type
  UnderMorphism = OverMorphism(dualCategory(C))(c)

  -- Also called: Coslice category, under category.
  underCategory : Category(UnderMorphism)
  underCategory = overCategory(dualCategory(C))(c)
