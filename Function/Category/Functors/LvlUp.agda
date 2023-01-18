open import Functional
import      Lvl
open import Structure.Operator
open import Structure.Setoid
open import Type

module Function.Category.Functors.LvlUp
  {ℓₑ : Lvl.Level → Lvl.Level → Lvl.Level}
  ⦃ equiv-func : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Equiv{ℓₑ ℓ₁ ℓ₂}(A → B) ⦄
  ⦃ [∘]-func : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

open import Function.Category
open import Structure.Categorical.Functor.Properties
open import Structure.Category.Functor
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Transitivity

private open module EquivFunc {ℓ₁}{ℓ₂}{A}{B} = Equiv(equiv-func{ℓ₁}{ℓ₂}{A}{B}) using ()

instance
  LvlUp-functor : ∀{ℓ₁ ℓ₂} → Functor(functionCategory)(functionCategory)(Lvl.Up{ℓ₁}{ℓ₂})
  Functor.map           LvlUp-functor f(Lvl.up x) = Lvl.up(f(x))
  Functor.map-function  (LvlUp-functor{ℓ₁}{ℓ₂}) {x}{y} = intro \fg → congruence₂-₂(_∘_)(Lvl.up) (congruence₂-₁(_∘_)(Lvl.Up.obj) fg)
  Functor.op-preserving LvlUp-functor = intro(reflexivity(_≡_))
  Functor.id-preserving LvlUp-functor = intro(reflexivity(_≡_))
