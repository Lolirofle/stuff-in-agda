module Structure.Category.Functor.Equiv where

import      Function.Equals
open        Function.Equals.Dependent
open import Logic
open import Logic.Predicate
import      Lvl
open import Type
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Functors as Functors
import      Structure.Category.Names as Names
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  ⦃ obj-equiv : Equiv(Obj) ⦄
  (Morphism : Obj → Obj → Type{ℓₘ})
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  where

  open Names.ArrowNotation(Morphism)
  open Functors.Wrapped

  instance -- TODO: Incorrect definition. The two `map` should also be the equivalent.
    functor-equiv : ∀{catₗ catᵣ : Category(Morphism)} → Equiv(catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
    Equiv._≡_ functor-equiv ([∃]-intro F₁) ([∃]-intro F₂) = Lvl.Up{ℓ₂ = ℓₘ}(F₁ ⊜ F₂)
    Reflexivity.proof (Equivalence.reflexivity (Equiv.[≡]-equivalence functor-equiv)) = Lvl.up(reflexivity(_≡_))
    Symmetry.proof (Equivalence.symmetry (Equiv.[≡]-equivalence functor-equiv)) (Lvl.up proof) = Lvl.up(symmetry(_⊜_) proof)
    Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence functor-equiv)) (Lvl.up p) (Lvl.up q) = Lvl.up(transitivity(_⊜_) p q)
  {-# WARNING_ON_USAGE functor-equiv "Incorrect definition" #-}

  {- TODO: Here, I try to define a more correct equivalence on functors, but apparently, heterogenous equality is neccessary for map-proof because F₁ is not identical to F₂. This probably means that categories have to be even more general. Morphisms have to have a "heterogenous Equiv".
  module _ {catₗ catᵣ : Category(Morphism)} (([∃]-intro F₁ ⦃ functor₁ ⦄) ([∃]-intro F₂ ⦃ functor₂ ⦄) : (catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)) where
    record _≡ᶠᵘⁿᶜᵗᵒʳ_ : Type where
      constructor intro
      field
        functor-proof : (F₁ ⊜ F₂)
        map-proof     : ∀{x y : Obj}{a : x ⟶ y} → (Functor.map(functor₁){x}{y} a ≡ Functor.map(functor₂){x}{y} a)
  -}
