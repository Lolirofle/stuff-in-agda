module Structure.Category.Dual where

open import Functional using (swap)
open import Sets.Setoid
open import Structure.Category
import      Structure.Operator.Properties as Properties
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

  open ArrowNotation
  open Category
  open module MorphismEquiv {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv{x}{y} ⦄) using () renaming (transitivity to morphism-transitivity ; symmetry to morphism-symmetry ; reflexivity to morphism-reflexivity)

  -- The opposite/dual category of a category.
  dual : Category(swap Morphism)
  _∘_ (dual) = swap(_∘_ (cat)) -- \{x}{y}{z} yz xy → _∘_ {z}{y}{x} xy yz
  id(dual) = id(cat)
  Properties.Identityₗ.proof(identityₗ(dual)) = Properties.Identityᵣ.proof(identityᵣ(cat))
  Properties.Identityᵣ.proof(identityᵣ(dual)) = Properties.Identityₗ.proof(identityₗ(cat))
  associativity(dual) {x}{y}{z}{w} {f}{g}{h} = symmetry(_≡_) (associativity(cat) {w}{z}{y}{x} {h}{g}{f})
