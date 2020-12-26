module Structure.Category.Functor.Contravariant where

open import Logic.Predicate
import      Lvl
open import Structure.Category.Functor
open import Structure.Category.Dual
open import Structure.Category
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₗₒ ℓₗₘ ℓᵣₒ ℓᵣₘ ℓₑ ℓₗₑ ℓᵣₑ : Lvl.Level
private variable Obj Objₗ Objᵣ : Type{ℓ}
private variable Morphism Morphismₗ Morphismᵣ : Objₗ → Objᵣ → Type{ℓ}


module _
  ⦃ morphism-equivₗ : ∀{x y : Objₗ} → Equiv{ℓₗₑ}(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y : Objᵣ} → Equiv{ℓᵣₑ}(Morphismᵣ x y) ⦄
  (Categoryₗ : Category(Morphismₗ))
  (Categoryᵣ : Category(Morphismᵣ))
  where

  ContravariantFunctor : (Objₗ → Objᵣ) → Type
  ContravariantFunctor = Functor (dualCategory Categoryₗ) Categoryᵣ
  module ContravariantFunctor = Functor{Categoryₗ = dualCategory Categoryₗ}{Categoryᵣ = Categoryᵣ}

module _
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv{ℓₑ}(Morphism x y) ⦄
  (Category : Category(Morphism))
  where

  ContravariantEndofunctor = ContravariantFunctor(Category)(Category)
  module ContravariantEndofunctor = ContravariantFunctor(Category)(Category)

_→ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₗₒ}{ℓₗₘ}{ℓₗₑ} → CategoryObject{ℓᵣₒ}{ℓᵣₘ}{ℓᵣₑ} → Type
catₗ →ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ catᵣ = ∃(ContravariantFunctor (CategoryObject.category(catₗ)) ((CategoryObject.category(catᵣ))))

⟲ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ_ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ} → Type
⟲ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ cat = cat →ᶜᵒⁿᵗʳᵃᵛᵃʳⁱᵃⁿᵗᶠᵘⁿᶜᵗᵒʳ cat

module _ (C₁ C₂ : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}) where
  open import Logic.Propositional
  open import Structure.Relator.Equivalence

  open CategoryObject ⦃ … ⦄
  open Category ⦃ … ⦄
  open ArrowNotation
  open Functor ⦃ … ⦄
  private open module MorphismEquiv₁ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv ⦃ C₁ ⦄ {x}{y} ⦄) using ()
  private open module MorphismEquiv₂ {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv ⦃ C₂ ⦄ {x}{y} ⦄) using ()

  instance _ = C₁
  instance _ = C₂

  contravariant-functor-def-dual : (dual(C₁) →ᶠᵘⁿᶜᵗᵒʳ C₂) ↔ (C₁ →ᶠᵘⁿᶜᵗᵒʳ dual(C₂))
  contravariant-functor-def-dual = [↔]-intro l r where
    l : (dual(C₁) →ᶠᵘⁿᶜᵗᵒʳ C₂) ← (C₁ →ᶠᵘⁿᶜᵗᵒʳ dual(C₂))
    ∃.witness (l ([∃]-intro F)) = F
    Functor.map           (∃.proof (l _)) = map
    Functor.map-function  (∃.proof (l _)) = map-function
    Functor.op-preserving (∃.proof (l _)) = op-preserving
    Functor.id-preserving (∃.proof (l _)) = id-preserving

    r : (dual(C₁) →ᶠᵘⁿᶜᵗᵒʳ C₂) → (C₁ →ᶠᵘⁿᶜᵗᵒʳ dual(C₂))
    ∃.witness (r ([∃]-intro F)) = F
    Functor.map           (∃.proof (r _)) = map
    Functor.map-function  (∃.proof (r _)) = map-function
    Functor.op-preserving (∃.proof (r _)) = op-preserving
    Functor.id-preserving (∃.proof (r _)) = id-preserving
