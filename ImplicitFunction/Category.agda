open import Functional.Implicit
open import Structure.Operator
open import Structure.Setoid
open import Type

module ImplicitFunction.Category
  {ℓₒ ℓₑ}
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ}(A ﹛→﹜ B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(_﹛∘﹜_ {X = A}{Y = B}{Z = C}) ⦄
  where

open import Logic.Propositional
import      Lvl
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Relator.Properties

private variable ℓ ℓₘ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

-- A category of types and implicit functions (functions with implicit domain space).
implicitFunctionCategory : Category{Obj = Type{ℓₒ}} (_﹛→﹜_) ⦃ equiv-func ⦄
Category._∘_            implicitFunctionCategory = _﹛∘﹜_
Category.id             implicitFunctionCategory = ﹛id﹜
Category.binaryOperator implicitFunctionCategory = [∘]-func
Category.associativity  implicitFunctionCategory = Morphism.intro \{a}{b}{c}{d} {f}{g}{h} → reflexivity(_) ⦃ Equiv.reflexivity equiv-func ⦄
Category.identity       implicitFunctionCategory = [∧]-intro (Morphism.intro (reflexivity(_) ⦃ Equiv.reflexivity equiv-func ⦄)) (Morphism.intro (reflexivity(_) ⦃ Equiv.reflexivity equiv-func ⦄))

ImplicitFunctionᶜᵃᵗ : CategoryObject
ImplicitFunctionᶜᵃᵗ = intro implicitFunctionCategory



-- TODO: Move below
open import Structure.Function
import Functional as Fn
module _
  {ℓₑₜ}
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑₜ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(Fn._∘_ {X = A}{Y = B}{Z = C}) ⦄
  ⦃ [﹛$﹜]-func : ∀{A B : Type{ℓₒ}} → Function(_﹛$﹜_ {X = A}{Y = B}) ⦄
  where

  open import Function.Category
  open import Logic.Predicate
  open import Structure.Categorical.Functor.Properties
  open import Structure.Category.Functor

  private open module EquivFunc {A}{B} = Equiv(equiv-func{A}{B}) using ()

  ﹛$﹜ᶠᵘⁿᶜᵗᵒʳ : ImplicitFunctionᶜᵃᵗ →ᶠᵘⁿᶜᵗᵒʳ Functionᶜᵃᵗ
  ﹛$﹜ᶠᵘⁿᶜᵗᵒʳ = [∃]-intro Fn.id where
    instance
      functor : Functor implicitFunctionCategory functionCategory Fn.id
      Functor.map functor = (_﹛$﹜_)
      Functor.map-function  functor = [﹛$﹜]-func
      Functor.op-preserving functor = intro(reflexivity(_≡_))
      Functor.id-preserving functor = intro(reflexivity(_≡_))
