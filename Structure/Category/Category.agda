module Structure.Category.Category where

open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
open import Function.Equals
import      Function.Equals.Proofs as Function
import      Lvl
open import Logic
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
import      Structure.Category.Names as Names
open import Structure.Category.Properties as Properties
import      Structure.Operator.Names as Names
import      Structure.Operator.Properties as Properties
import      Structure.Relator.Names as Names
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Category.Functor
import      Structure.Category.Functor.Functors as Functors
open import Structure.Category.NaturalTransformation
open import Syntax.Transitivity
open import Type

module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  ⦃ obj-equiv : Equiv(Obj) ⦄
  (Morphism : Obj → Obj → Type{ℓₘ})
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  where

  open Names.ArrowNotation(Morphism)
  open Functors.Wrapped

  instance
    functor-equiv : ∀{catₗ catᵣ : Category(Morphism)} → Equiv(catₗ →ᶠᵘⁿᶜᵗᵒʳ catᵣ)
    Equiv._≡_ functor-equiv ([∃]-intro F₁) ([∃]-intro F₂) = Lvl.Up{ℓ₂ = ℓₘ}(F₁ ⊜ F₂)
    Dependent._⊜_.proof (Lvl.Up.obj (Reflexivity.proof (Equivalence.reflexivity (Equiv.[≡]-equivalence functor-equiv)))) = reflexivity(_≡_)
    Dependent._⊜_.proof (Lvl.Up.obj (Symmetry.proof (Equivalence.symmetry (Equiv.[≡]-equivalence functor-equiv)) (Lvl.up (Dependent.intro proof)))) = symmetry(_≡_) proof
    Dependent._⊜_.proof (Lvl.Up.obj (Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence functor-equiv)) (Lvl.up (Dependent.intro p)) (Lvl.up (Dependent.intro q)))) = transitivity(_≡_) p q

  categoryCategory : Category{Obj = Category(_⟶_)} (_→ᶠᵘⁿᶜᵗᵒʳ_)
  Category._∘_ categoryCategory = _∘ᶠᵘⁿᶜᵗᵒʳ_
  Category.id  categoryCategory = idᶠᵘⁿᶜᵗᵒʳ
  Dependent._⊜_.proof (Lvl.Up.obj (BinaryOperator.congruence (Category.binaryOperator categoryCategory) {[∃]-intro F₁} {[∃]-intro F₂} (Lvl.up (Dependent.intro proof-F)) {[∃]-intro G₁} {[∃]-intro G₂} (Lvl.up (Dependent.intro proof-G)))) {obj} =
    F₁(G₁(obj)) 🝖-[ _⊜_.proof (Function.[⊜][∘]-binaryOperator-raw ⦃ _ ⦄ ⦃ _ ⦄ ⦃ test ⦄ (intro proof-F) (intro(proof-G {x = obj}))){x = obj} ]
    F₂(G₂(obj)) 🝖-end
    where postulate test : Function(F₂)
  Category.associativity categoryCategory = {!!}
  Category.identity categoryCategory = {!!}
