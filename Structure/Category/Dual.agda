import      Lvl

module Structure.Category.Dual {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Data.Tuple as Tuple using ()
open import Functional using (swap)
open import Structure.Category
open import Structure.Categorical.Names
open import Structure.Categorical.Properties
import      Structure.Operator.Properties as Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

module _
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄
  (cat : Category(Morphism))
  where

  open Category.ArrowNotation(cat)
  open Category(cat)
  private open module MorphismEquiv {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

  -- The opposite/dual category of a category.
  dualCategory : Category(_⟵_)
  Category._∘_ dualCategory = swap(_∘_)
  Category.id  dualCategory = id
  BinaryOperator.congruence             (Category.binaryOperator dualCategory) p₁ p₂ = congruence₂(_∘_) p₂ p₁
  Morphism.Associativity.proof          (Category.associativity  dualCategory)  = symmetry(_≡_) (Morphism.associativity(_∘_))
  Morphism.Identityₗ.proof (Tuple.left  (Category.identity       dualCategory)) = Morphism.identity-right(_∘_)(id)
  Morphism.Identityᵣ.proof (Tuple.right (Category.identity       dualCategory)) = Morphism.identity-left (_∘_)(id)

dual : CategoryObject{ℓₒ}{ℓₘ} → CategoryObject{ℓₒ}{ℓₘ}
dual(intro cat) = intro(dualCategory cat)
