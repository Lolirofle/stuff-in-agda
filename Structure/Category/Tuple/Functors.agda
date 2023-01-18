import      Lvl
open import Structure.Category

module Structure.Category.Tuple.Functors
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Data.Tuple as Type using (_,_)
open import Data.Tuple.Category
import      Functional as Fn
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Categorical.Properties
open import Structure.Category.Functor
open import Structure.Category.Tuple {C = C}
open import Structure.Category.Tuple.Proofs {C = C}
open import Structure.Function
open import Structure.IndexedOperator.Properties.Preserving
open import Structure.Operator
open import Structure.Setoid
open import Syntax.Transitivity

module _
  {_⨯_}
  ⦃ tuple : Tuple(_⨯_) ⦄
  where

  open Tuple(tuple)
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using () public

  map-functor : Functor ⦃ _ ⦄ (tupleCategory category category) category (Type.uncurry(_⨯_))
  Functor.map map-functor = Type.uncurry(map)
  Functor.map-function map-functor = intro \([∧]-intro p q) → [<,>]-function (congruence₂-₁(_∘_)(projₗ) p) (congruence₂-₁(_∘_)(projᵣ) q)
  Functor.op-preserving map-functor = intro \{ {f₁ , f₂}{g₁ , g₂} →
    map(f₁ ∘ g₁) (f₂ ∘ g₂)                                            🝖[ _≡_ ]-[]
    ((f₁ ∘ g₁) ∘ projₗ) <,> ((f₂ ∘ g₂) ∘ projᵣ)                       🝖[ _≡_ ]-[ uniqueness-condition
      (
        projₗ ∘ (((f₁ ∘ projₗ) <,> (f₂ ∘ projᵣ)) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ))) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
        (projₗ ∘ ((f₁ ∘ projₗ) <,> (f₂ ∘ projᵣ))) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) projₗ-condition ]
        (f₁ ∘ projₗ) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ))                              🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
        f₁ ∘ (projₗ ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ)))                              🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) projₗ-condition ]
        f₁ ∘ (g₁ ∘ projₗ)                                                           🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
        (f₁ ∘ g₁) ∘ projₗ                                                           🝖-end
      )
      (
        projᵣ ∘ (((f₁ ∘ projₗ) <,> (f₂ ∘ projᵣ)) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ))) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
        (projᵣ ∘ ((f₁ ∘ projₗ) <,> (f₂ ∘ projᵣ))) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) projᵣ-condition ]
        (f₂ ∘ projᵣ) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ))                              🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
        f₂ ∘ (projᵣ ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ)))                              🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(_) projᵣ-condition ]
        f₂ ∘ (g₂ ∘ projᵣ)                                                           🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
        (f₂ ∘ g₂) ∘ projᵣ                                                           🝖-end
      )
    ]-sym
    ((f₁ ∘ projₗ) <,> (f₂ ∘ projᵣ)) ∘ ((g₁ ∘ projₗ) <,> (g₂ ∘ projᵣ)) 🝖[ _≡_ ]-[]
    map f₁ f₂ ∘ map g₁ g₂                                             🝖-end
    }
  Functor.id-preserving map-functor = intro Fn.$
    map id id                     🝖[ _≡_ ]-[]
    (id ∘ projₗ) <,> (id ∘ projᵣ) 🝖[ _≡_ ]-[ [<,>]-function (Morphism.identityₗ(_∘_)(id)) (Morphism.identityₗ(_∘_)(id)) ]
    projₗ <,> projᵣ               🝖[ _≡_ ]-[ [<,>]-proj-inverse ]
    id                            🝖-end

  ⨯ᶠᵘⁿᶜᵗᵒʳ : (C ⨯ᶜᵃᵗ C) →ᶠᵘⁿᶜᵗᵒʳ C
  ⨯ᶠᵘⁿᶜᵗᵒʳ = [∃]-intro _ ⦃ map-functor ⦄
