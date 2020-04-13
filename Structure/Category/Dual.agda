module Structure.Category.Dual where

open import Data.Tuple as Tuple using ()
open import Functional using (swap)
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Names
open import Structure.Category.Properties
import      Structure.Operator.Properties as Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

module _
  {ℓₒ ℓₘ}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  (cat : Category(Morphism))
  where

  open Category.ArrowNotation(cat)
  open Category(cat)
  private open module MorphismEquiv {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

  -- The opposite/dual category of a category.
  dual : Category(_⟵_)
  Category._∘_ dual = swap(_∘_)
  Category.id dual = id
  BinaryOperator.congruence             (Category.binaryOperator dual) p₁ p₂ = [≡]-with2(_∘_) p₂ p₁
  Morphism.Associativity.proof          (Category.associativity  dual)  = symmetry(_≡_) (Morphism.associativity(_∘_))
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity       dual)) = Morphism.identity-right(_∘_)(id)
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity       dual)) = Morphism.identity-left (_∘_)(id)
