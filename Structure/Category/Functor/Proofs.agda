module Structure.Category.Functor.Proofs where

open import Data.Tuple as Tuple using (_,_)
open import Functional using (_$_)
open import Logic.Predicate
import      Lvl
open import Structure.Categorical.Functor.Properties
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Category.Functor.Equiv
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₗₑ ℓᵣₑ : Lvl.Level
private variable Obj Obj₁ Obj₂ Obj₃ : Type{ℓ}
private variable Morphism Morphism₁ Morphism₂ Morphism₃ : Obj → Obj → Type{ℓ}

module _
  ⦃ morphism-equiv₁ : ∀{x y} → Equiv{ℓₗₑ}(Morphism₁ x y) ⦄
  ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓᵣₑ}(Morphism₂ x y) ⦄
  {cat₁ : Category(Morphism₁)}
  {cat₂ : Category(Morphism₂)}
  (F : Obj₁ → Obj₂)
  ⦃ functor : Functor(cat₁)(cat₂)(F) ⦄
  where

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄
  open Functor(functor)
  private open module MorphismEquivₗ {x}{y} = Equiv(morphism-equiv₁{x}{y}) using () renaming (_≡_ to _≡ₗₘ_)
  private open module MorphismEquivᵣ {x}{y} = Equiv(morphism-equiv₂{x}{y}) using () renaming (_≡_ to _≡ᵣₘ_)

  private instance _ = cat₁
  private instance _ = cat₂
  private variable x y : Obj₁

  isomorphism-preserving : ∀{f : x ⟶ y} → Morphism.Isomorphism ⦃ \{x y} → morphism-equiv₁ {x}{y} ⦄ (_∘_)(id)(f) → Morphism.Isomorphism ⦃ \{x y} → morphism-equiv₂ {x}{y} ⦄ (_∘_)(id)(map f)
  ∃.witness (isomorphism-preserving ([∃]-intro g)) = map g
  ∃.proof (isomorphism-preserving {f = f} iso@([∃]-intro g)) =
    (Morphism.intro $
      map g ∘ map f 🝖-[ Preserving.proof op-preserving ]-sym
      map(g ∘ f)    🝖-[ congruence₁(map) (inverseₗ(f)(g)) ]
      map id        🝖-[ Preserving.proof id-preserving ]
      id            🝖-end
    ) , (Morphism.intro $
      map f ∘ map g 🝖-[ Preserving.proof op-preserving ]-sym
      map(f ∘ g)    🝖-[ congruence₁(map) (inverseᵣ(f)(g)) ]
      map id        🝖-[ Preserving.proof id-preserving ]
      id            🝖-end
    )
    where
      open Morphism.OperModule (\{x : Obj₁} → _∘_ {x = x})
      open Morphism.IdModule   (\{x : Obj₁} → _∘_ {x = x})(id)
      open Morphism.Isomorphism(\{x : Obj₁} → _∘_ {x = x})(id)(f)
      instance _ = iso
