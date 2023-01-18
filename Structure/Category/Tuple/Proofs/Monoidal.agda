import      Lvl
open import Structure.Category

module Structure.Category.Tuple.Proofs.Monoidal
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (let open CategoryObject(C)) (let open ArrowNotation)
  where

open import Data.Tuple as Type using (_,_)
open import Data.Tuple.Category
import      Functional as Fn
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Categorical.Properties
import      Structure.Category.Functor.Functors
open        Structure.Category.Functor.Functors.Wrapped
open import Structure.Category.Monoidal
open import Structure.Category.NaturalIsomorphism
open import Structure.Category.NaturalIsomorphism.Functions
open import Structure.Category.NaturalTransformation
open import Structure.Category.Tuple {C = C}
open import Structure.Category.Tuple.Functors {C = C}
open import Structure.Category.Tuple.Proofs {C = C}
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Properties.MereProposition
open import Type.Properties.Proofs
open import Type.Properties.Singleton

-- TODO: All these proofs can probably be automated because they just check if the normal forms are equal
module _
  {_⨯_}
  ⦃ tuple : Tuple(_⨯_) ⦄
  where

  open Tuple(tuple)
  private open module MorphismEquiv{x}{y} = Equiv(morphism-equiv{x}{y}) using () public

  associatorᴺᵀ : ((⨯ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.mapLeft ⨯ᶠᵘⁿᶜᵗᵒʳ) ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.associateLeft) ↔ᴺᵀ (⨯ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.mapRight ⨯ᶠᵘⁿᶜᵗᵒʳ)
  associatorᴺᵀ = let l = projₗ ; r = projᵣ in [∃]-intro
    (\_ → (associateLeft , associateRight))
    ⦃ NaturalIsomorphism-introᵣ _ _ _
      ⦃ intro \{ {x}{y}{(f , (g , h))} →
        ((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ 🝖 [<,>]-function
          (
            (l ∘ l) ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
            l ∘ (l ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(l) projₗ-condition ]
            l ∘ (((f ∘ l) <,> (g ∘ r)) ∘ l)                     🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
            (l ∘ ((f ∘ l) <,> (g ∘ r))) ∘ l                     🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(l) projₗ-condition ]
            (f ∘ l) ∘ l                                         🝖-end
          )
          (
            ((r ∘ l) <,> r) ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ 🝖 [<,>]-function
              (
                (r ∘ l) ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
                r ∘ (l ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(r) projₗ-condition ]
                r ∘ (((f ∘ l) <,> (g ∘ r)) ∘ l)                     🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
                (r ∘ ((f ∘ l) <,> (g ∘ r))) ∘ l                     🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(l) projᵣ-condition ]
                (g ∘ r) ∘ l 🝖-end
              )
              (
                r ∘ ((((f ∘ l) <,> (g ∘ r)) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ projᵣ-condition ]
                h ∘ r 🝖-end
              )
            ]
            ((g ∘ r) ∘ l) <,> (h ∘ r) 🝖-end
          )
        ]
        ((f ∘ l) ∘ l) <,> (((g ∘ r) ∘ l) <,> (h ∘ r)) 🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ 🝖 [<,>]-function
          (
            (f ∘ l) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
            f ∘ (l ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(f) projₗ-condition ]
            f ∘ (l ∘ l)                             🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
            (f ∘ l) ∘ l                             🝖-end
          )
          (
            (((g ∘ l) <,> (h ∘ r)) ∘ r) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
            ((g ∘ l) <,> (h ∘ r)) ∘ (r ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)((g ∘ l) <,> (h ∘ r)) projᵣ-condition ]
            ((g ∘ l) <,> (h ∘ r)) ∘ ((r ∘ l) <,> r)                     🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ 🝖 [<,>]-function
              (
                (g ∘ l) ∘ ((r ∘ l) <,> r) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
                g ∘ (l ∘ ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(g) projₗ-condition ]
                g ∘ (r ∘ l)               🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]-sym
                (g ∘ r) ∘ l               🝖-end
              )
              (
                (h ∘ r) ∘ ((r ∘ l) <,> r) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
                h ∘ (r ∘ ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(h) projᵣ-condition ]
                h ∘ r                     🝖-end
              )
            ]
            (((g ∘ r) ∘ l) <,> (h ∘ r)) 🝖-end
          )
        ]-sym
        ((f ∘ l) <,> (((g ∘ l) <,> (h ∘ r)) ∘ r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖-end
      } ⦄
      ⦃ \{x} → [∧]-intro
        (Morphism.intro Fn.$
          ((l <,> (l ∘ r)) <,> (r ∘ r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))                                                                     🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ ]
          ((l <,> (l ∘ r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))) <,> ((r ∘ r) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)))                                   🝖[ _≡_ ]-[ [<,>]-function [∘][<,>]-distributivityᵣ (Morphism.associativity(_∘_)) ]
          ((l ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))) <,> ((l ∘ r) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)))) <,> (r ∘ (r ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)))) 🝖[ _≡_ ]-[ [<,>]-function ([<,>]-function projₗ-condition (Morphism.associativity(_∘_))) (congruence₂-₂(_∘_)(r) projᵣ-condition) ]
          ((l ∘ l) <,> (l ∘ (r ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))))) <,> (r ∘ ((r ∘ l) <,> r))                                                 🝖[ _≡_ ]-[ [<,>]-function ([<,>]-function (reflexivity(_≡_)) (congruence₂-₂(_∘_)(l) projᵣ-condition)) projᵣ-condition ]
          ((l ∘ l) <,> (l ∘ ((r ∘ l) <,> r))) <,> r                                                                                         🝖[ _≡_ ]-[ [<,>]-function ([<,>]-function (reflexivity(_≡_)) projₗ-condition) (reflexivity(_≡_)) ]
          ((l ∘ l) <,> (r ∘ l)) <,> r                                                                                                       🝖[ _≡_ ]-[ [<,>]-function [∘][<,>]-distributivityᵣ (reflexivity(_≡_)) ]-sym
          ((l <,> r) ∘ l) <,> r                                                                                                             🝖[ _≡_ ]-[ [<,>]-function (congruence₂-₁(_∘_)(l) [<,>]-proj-inverse) (reflexivity(_≡_)) ]
          (id ∘ l) <,> r                                                                                                                    🝖[ _≡_ ]-[ [<,>]-function (Morphism.identityₗ(_∘_)(id)) (reflexivity(_≡_)) ]
          l <,> r                                                                                                                           🝖[ _≡_ ]-[ [<,>]-proj-inverse ]
          id                                                                                                                                🝖-end
        )
        (Morphism.intro Fn.$
          ((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ ((l <,> (l ∘ r)) <,> (r ∘ r))                                                                     🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ ]
          ((l ∘ l) ∘ ((l <,> (l ∘ r)) <,> (r ∘ r))) <,> (((r ∘ l) <,> r) ∘ ((l <,> (l ∘ r)) <,> (r ∘ r)))                                   🝖[ _≡_ ]-[ [<,>]-function (Morphism.associativity(_∘_)) [∘][<,>]-distributivityᵣ ]
          (l ∘ (l ∘ ((l <,> (l ∘ r)) <,> (r ∘ r)))) <,> (((r ∘ l) ∘ ((l <,> (l ∘ r)) <,> (r ∘ r))) <,> (r ∘ ((l <,> (l ∘ r)) <,> (r ∘ r)))) 🝖[ _≡_ ]-[ [<,>]-function (congruence₂-₂(_∘_)(l) projₗ-condition) ([<,>]-function (Morphism.associativity(_∘_)) projᵣ-condition) ]
          (l ∘ (l <,> (l ∘ r))) <,> ((r ∘ (l ∘ ((l <,> (l ∘ r)) <,> (r ∘ r)))) <,> (r ∘ r))                                                 🝖[ _≡_ ]-[ [<,>]-function projₗ-condition ([<,>]-function (congruence₂-₂(_∘_)(r) projₗ-condition) (reflexivity(_≡_))) ]
          l <,> ((r ∘ (l <,> (l ∘ r))) <,> (r ∘ r))                                                                                         🝖[ _≡_ ]-[ [<,>]-function (reflexivity(_≡_)) ([<,>]-function projᵣ-condition (reflexivity(_≡_))) ]
          l <,> ((l ∘ r) <,> (r ∘ r))                                                                                                       🝖[ _≡_ ]-[ [<,>]-function (reflexivity(_≡_)) [∘][<,>]-distributivityᵣ ]-sym
          l <,> ((l <,> r) ∘ r)                                                                                                             🝖[ _≡_ ]-[ [<,>]-function (reflexivity(_≡_)) (congruence₂-₁(_∘_)(r) [<,>]-proj-inverse) ]
          l <,> (id ∘ r)                                                                                                                    🝖[ _≡_ ]-[ [<,>]-function (reflexivity(_≡_)) (Morphism.identityₗ(_∘_)(id)) ]
          l <,> r                                                                                                                           🝖[ _≡_ ]-[ [<,>]-proj-inverse ]
          id                                                                                                                                 🝖-end
        )
      ⦄
    ⦄

  module _ {𝟏} ⦃ terminal : Object.Terminal(_⟶_)(𝟏) ⦄ where
    unitorₗᴺᵀ : (⨯ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constₗ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ
    unitorₗᴺᵀ = [∃]-intro
      (\x → ((Object.terminalMorphism(_⟶_)(x) <,> id) , projᵣ))
      ⦃ NaturalIsomorphism-introᵣ _ _ _
        ⦃ intro \{x}{y}{f} →
          projᵣ ∘ ((id ∘ projₗ) <,> (f ∘ projᵣ)) 🝖[ _≡_ ]-[ projᵣ-condition ]
          f ∘ projᵣ                              🝖-end
        ⦄
        ⦃ \{x} → [∧]-intro
          (Morphism.intro Fn.$
            (Object.terminalMorphism(_⟶_)(x) <,> id) ∘ projᵣ           🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ ]
            (Object.terminalMorphism(_⟶_)(x) ∘ projᵣ) <,> (id ∘ projᵣ) 🝖[ _≡_ ]-[ uniqueness-condition
              (uniqueness((𝟏 ⨯ x) ⟶ 𝟏) ⦃ inst = unit-is-prop ⦄)
              (Morphism.identityᵣ(_∘_)(id) 🝖 symmetry(_≡_) (Morphism.identityₗ(_∘_)(id)))
            ]-sym
            id                                                         🝖-end
          )
          (Morphism.intro Fn.$
            projᵣ ∘ (Object.terminalMorphism(_⟶_)(x) <,> id) 🝖[ _≡_ ]-[ projᵣ-condition ]
            id                                               🝖-end
          )
        ⦄
      ⦄

    unitorᵣᴺᵀ : (⨯ᶠᵘⁿᶜᵗᵒʳ ∘ᶠᵘⁿᶜᵗᵒʳ Tupleᶜᵃᵗ.constᵣ 𝟏) ↔ᴺᵀ idᶠᵘⁿᶜᵗᵒʳ
    unitorᵣᴺᵀ = [∃]-intro
      (\x → ((id <,> Object.terminalMorphism(_⟶_)(x)) , projₗ))
      ⦃ NaturalIsomorphism-introᵣ _ _ _
        ⦃ intro \{x}{y}{f} →
          projₗ ∘ ((f ∘ projₗ) <,> (id ∘ projᵣ)) 🝖[ _≡_ ]-[ projₗ-condition ]
          f ∘ projₗ                              🝖-end
        ⦄
        ⦃ \{x} → [∧]-intro
          (Morphism.intro Fn.$
            (id <,> Object.terminalMorphism(_⟶_)(x)) ∘ projₗ           🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ ]
            (id ∘ projₗ) <,> (Object.terminalMorphism(_⟶_)(x) ∘ projₗ) 🝖[ _≡_ ]-[ uniqueness-condition
              (Morphism.identityᵣ(_∘_)(id) 🝖 symmetry(_≡_) (Morphism.identityₗ(_∘_)(id)))
              (uniqueness((x ⨯ 𝟏) ⟶ 𝟏) ⦃ inst = unit-is-prop ⦄)
            ]-sym
            id                                                         🝖-end
          )
          (Morphism.intro Fn.$
            projₗ ∘ (id <,> Object.terminalMorphism(_⟶_)(x)) 🝖[ _≡_ ]-[ projₗ-condition ]
            id                                               🝖-end
          )
        ⦄
      ⦄

    open import Structure.Category.Functor

    monoidal : Monoidalᶜᵃᵗ(C) -- TODO: I don't have time for this now. Maybe for another time
    Monoidalᶜᵃᵗ.productFunctor monoidal = ⨯ᶠᵘⁿᶜᵗᵒʳ
    Monoidalᶜᵃᵗ.unitObject     monoidal = 𝟏
    MonoidalCategory.associator (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = associatorᴺᵀ
    MonoidalCategory.unitorₗ    (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = unitorₗᴺᵀ
    MonoidalCategory.unitorᵣ    (Monoidalᶜᵃᵗ.monoidalCategory monoidal) = unitorᵣᴺᵀ
    MonoidalCategory.associativity-condition (Monoidalᶜᵃᵗ.monoidalCategory monoidal) {x}{y}{z}{w} = let l = projₗ ; r = projᵣ in
      ((id ∘ l) <,> (((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ ((((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ l) <,> (id ∘ r)) 🝖[ _≡_ ]-[ {!!} ]
      ((l ∘ l) <,> ((r ∘ l) <,> r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖-end
    MonoidalCategory.unitality-condition     (Monoidalᶜᵃᵗ.monoidalCategory monoidal) {x}{y} = let l = projₗ ; r = projᵣ in
      ((id ∘ l) <,> (r ∘ r)) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ [∘][<,>]-distributivityᵣ 🝖 [<,>]-function
          (
            (id ∘ l) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ congruence₂-₁(_∘_)(_) (Morphism.identityₗ(_∘_)(id)) ]
            l ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ projₗ-condition ]
            l ∘ l 🝖-end
          )
          (
            (r ∘ r) ∘ ((l ∘ l) <,> ((r ∘ l) <,> r)) 🝖[ _≡_ ]-[ Morphism.associativity(_∘_) ]
            r ∘ (r ∘ ((l ∘ l) <,> ((r ∘ l) <,> r))) 🝖[ _≡_ ]-[ congruence₂-₂(_∘_)(r) projᵣ-condition ]
            r ∘ ((r ∘ l) <,> r)                     🝖[ _≡_ ]-[ projᵣ-condition ]
            r                                       🝖[ _≡_ ]-[ Morphism.identityₗ(_∘_)(id) ]-sym
            id ∘ r                                  🝖-end
          )
      ]
      ((l ∘ l) <,> (id ∘ r)) 🝖-end
