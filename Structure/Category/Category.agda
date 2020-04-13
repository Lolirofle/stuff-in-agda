module Structure.Category.Category where

open import Data.Tuple as Tuple using ()
open import Functional           using () renaming (id to idᶠⁿ)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠⁿ_)
open import Function.Equals
import      Function.Equals.Proofs as Function
import      Function.Proofs as Function
import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Category
open import Structure.Category.Functor.Equiv
import      Structure.Category.Names as Names
open import Structure.Category.Properties as Properties
import      Structure.Operator.Names as Names
import      Structure.Operator.Properties as Properties
open import Structure.Operator
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
  ⦃ functor-equiv : ∀{x y} → Equiv(x →ᶠᵘⁿᶜᵗᵒʳ y) ⦄
  where

  open Names.ArrowNotation(Morphism)
  open Functors.Wrapped

  categoryCategory : Category{Obj = Category(_⟶_)} (_→ᶠᵘⁿᶜᵗᵒʳ_)
  Category._∘_ categoryCategory = _∘ᶠᵘⁿᶜᵗᵒʳ_
  Category.id categoryCategory = idᶠᵘⁿᶜᵗᵒʳ
  BinaryOperator.congruence (Category.binaryOperator categoryCategory) p₁ p₂ = {!!}
  Morphism.Associativity.proof (Category.associativity categoryCategory) = {!reflexivity(_≡_)!}
  Category.identity categoryCategory = {!!}

  {- TODO: Resolve the problem in Category.Functor.Equiv if possible
  categoryCategory : Category{Obj = Category(_⟶_)} (_→ᶠᵘⁿᶜᵗᵒʳ_)
  Category._∘_ categoryCategory = _∘ᶠᵘⁿᶜᵗᵒʳ_
  Category.id  categoryCategory = idᶠᵘⁿᶜᵗᵒʳ
  Dependent._⊜_.proof (Lvl.Up.obj (BinaryOperator.congruence (Category.binaryOperator categoryCategory) {[∃]-intro F₁} {[∃]-intro F₂} (Lvl.up (Dependent.intro proof-F)) {[∃]-intro G₁} {[∃]-intro G₂} (Lvl.up (Dependent.intro proof-G)))) {obj} =
    F₁(G₁(obj)) 🝖-[ _⊜_.proof (Function.[⊜][∘]-binaryOperator-raw (intro proof-F) (intro(proof-G {x = obj}))){x = obj} ]
    F₂(G₂(obj)) 🝖-end
  Morphism.Associativity.proof (Category.associativity categoryCategory) {x = _}{_}{_}{_} {[∃]-intro F} {[∃]-intro G} {[∃]-intro H} = Lvl.up(Function.[∘]-associativity {f = F}{g = G}{h = H})
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity categoryCategory)) = Lvl.up(Function.[∘]-identityₗ)
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity categoryCategory)) = Lvl.up(Function.[∘]-identityᵣ)
  -}
