module Structure.Category.Functor.Functors.Proofs where

import      Functional as Fn
import      Function.Equals
open        Function.Equals.Dependent
open import Function.Equals.Proofs
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Relator.Equals.Proofs.Equivalence
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Equiv
open import Structure.Category.Functor.Functors
open import Structure.Category.Morphism.IdTransport
open import Structure.Category.NaturalTransformation
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓₒ ℓₘ ℓₑ : Lvl.Level
private variable A B C : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}

open CategoryObject
open Category ⦃ … ⦄
open Functor ⦃ … ⦄

module _ where
  open Wrapped

  -- TODO: Prove transport-of-congruenced-bifunctor
  [∘ᶠᵘⁿᶜᵗᵒʳ]-binaryOperator : BinaryOperator(_∘ᶠᵘⁿᶜᵗᵒʳ_ {A = A}{B = B}{C = C})
  _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (BinaryOperator.congruence ([∘ᶠᵘⁿᶜᵗᵒʳ]-binaryOperator {A = A} {B = B} {C = C}) {[∃]-intro F₁} {[∃]-intro F₂} {[∃]-intro G₁} {[∃]-intro G₂} (intro fp₁ mp₁) (intro fp₂ mp₂)) = congruence₂(Fn._∘_) ⦃ [⊜][∘]-binaryOperator ⦃ function = [≡]-function ⦄ ⦄ fp₁ fp₂ where
    instance _ = [≡]-equiv {T = Object(B)}
    instance _ = [≡]-equiv {T = Object(C)}
  NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (BinaryOperator.congruence ([∘ᶠᵘⁿᶜᵗᵒʳ]-binaryOperator {A = A} {B = B} {C = C}) {[∃]-intro F₁}{[∃]-intro F₂} {[∃]-intro G₁}{[∃]-intro G₂} (intro fp₁ mp₁) (intro fp₂ mp₂))) {x}{y} {f} = anything {-
    transport C (_⊜_.proof (congruence₂(Fn._∘_) ⦃ [⊜][∘]-binaryOperator ⦃ function = [≡]-function _ ⦄ ⦄ fp₁ fp₂)) ∘ map(map f)      🝖-[ {!x₂ y₂!} ]
    map(map f) ∘ transport C (congruence₁-op (Object C) (λ v v₁ → {!v!}) (_⊜_.proof fp₁) (_⊜_.proof fp₂)) 🝖-[ {!!} ]
    map(map f) ∘ transport C (_⊜_.proof (congruence₂(Fn._∘_) ⦃ [⊜][∘]-binaryOperator ⦃ function = [≡]-function _ ⦄ ⦄ fp₁ fp₂)) 🝖-end-}
    where
      postulate anything : ∀{ℓ}{a : Type{ℓ}} → a
      open module MorphismEquivB {x}{y} = Equiv(morphism-equiv B {x}{y}) using () renaming (_≡_ to _≡B_)
      open module MorphismEquivC {x}{y} = Equiv(morphism-equiv C {x}{y}) using () renaming (_≡_ to _≡C_)
      instance _ = category A
      instance _ = category B
      instance _ = category C
      instance _ = [≡]-equiv {T = Object B}
      instance _ = [≡]-equiv {T = Object C}
      -- congruence₁-op

  instance
    [∘ᶠᵘⁿᶜᵗᵒʳ]-identityₗ : Morphism.Identityₗ {Obj = CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (\{A} → _∘ᶠᵘⁿᶜᵗᵒʳ_ {A = A})(idᶠᵘⁿᶜᵗᵒʳ)
    _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Morphism.Identityₗ.proof ([∘ᶠᵘⁿᶜᵗᵒʳ]-identityₗ) {y = B}) = reflexivity(_⊜_) where
      instance _ = [≡]-equiv {T = Object(B)}
    NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Morphism.Identityₗ.proof [∘ᶠᵘⁿᶜᵗᵒʳ]-identityₗ {A} {B} {[∃]-intro F})) {x} {y} {f} =
      id ∘ map f 🝖-[ Morphism.identityₗ(_∘_)(id) ]
      map f      🝖-[ Morphism.identityᵣ(_∘_)(id) ]-sym
      map f ∘ id 🝖-end
      where
        open module MorphismEquivB {x}{y} = Equiv(morphism-equiv B {x}{y}) using () renaming (_≡_ to _≡B_)
        instance _ = category A
        instance _ = category B

  instance
    [∘ᶠᵘⁿᶜᵗᵒʳ]-identityᵣ : Morphism.Identityᵣ {Obj = CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (\{A} → _∘ᶠᵘⁿᶜᵗᵒʳ_ {A = A})(idᶠᵘⁿᶜᵗᵒʳ)
    _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Morphism.Identityᵣ.proof ([∘ᶠᵘⁿᶜᵗᵒʳ]-identityᵣ) {y = B}) = reflexivity(_⊜_) where
      instance _ = [≡]-equiv {T = Object(B)}
    NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Morphism.Identityᵣ.proof [∘ᶠᵘⁿᶜᵗᵒʳ]-identityᵣ {A} {B} {[∃]-intro F})) {x} {y} {f} = 
      id ∘ map f 🝖-[ Morphism.identityₗ(_∘_)(id) ]
      map f      🝖-[ Morphism.identityᵣ(_∘_)(id) ]-sym
      map f ∘ id 🝖-end
      where
        open module MorphismEquivB {x}{y} = Equiv(morphism-equiv B {x}{y}) using () renaming (_≡_ to _≡B_)
        instance _ = category A
        instance _ = category B


  instance
    [∘ᶠᵘⁿᶜᵗᵒʳ]-identity : Morphism.Identity {Obj = CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (\{A} → _∘ᶠᵘⁿᶜᵗᵒʳ_ {A = A})(idᶠᵘⁿᶜᵗᵒʳ)
    [∘ᶠᵘⁿᶜᵗᵒʳ]-identity = [∧]-intro [∘ᶠᵘⁿᶜᵗᵒʳ]-identityₗ [∘ᶠᵘⁿᶜᵗᵒʳ]-identityᵣ

  instance
    [∘ᶠᵘⁿᶜᵗᵒʳ]-associativity : Morphism.Associativity {Obj = CategoryObject{ℓₒ}{ℓₘ}{ℓₑ}} (\{A B C} → _∘ᶠᵘⁿᶜᵗᵒʳ_ {A = A}{B = B}{C = C})
    _≡ᶠᵘⁿᶜᵗᵒʳ_.functor-proof (Morphism.Associativity.proof [∘ᶠᵘⁿᶜᵗᵒʳ]-associativity {w = D}) = reflexivity(_⊜_) where
      instance _ = [≡]-equiv {T = Object(D)}
    NaturalTransformation.natural (_≡ᶠᵘⁿᶜᵗᵒʳ_.map-proof (Morphism.Associativity.proof [∘ᶠᵘⁿᶜᵗᵒʳ]-associativity {A}{B}{C}{D} {[∃]-intro F}{[∃]-intro G}{[∃]-intro H})) {x}{y}{f} =
      id ∘ map(map(map f)) 🝖-[ Morphism.identityₗ(_∘_)(id) ]
      map(map(map f))      🝖-[ Morphism.identityᵣ(_∘_)(id) ]-sym
      map(map(map f)) ∘ id 🝖-end
      where
        open module MorphismEquivₗ {x}{y} = Equiv(morphism-equiv D {x}{y}) using () renaming (_≡_ to _≡D_)
        instance _ = category A
        instance _ = category B
        instance _ = category C
        instance _ = category D
