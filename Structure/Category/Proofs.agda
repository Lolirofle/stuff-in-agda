module Structure.Category.Proofs where

import      Lvl
open import Data
open import Functional using (const ; swap)
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Category
import      Structure.Operator.Properties as Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

module _
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  (C : Category(Morphism))
  where

  open Category(C)
  open ArrowNotation(Morphism)
  open module [≡]-Equivalence {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equiv{x}{y} ⦄) using () renaming (transitivity to [≡]-transitivity ; symmetry to [≡]-symmetry ; reflexivity to [≡]-reflexivity)

  id-automorphism : ∀{x : Obj} → Automorphism(id{x})
  Category.Isomorphism.inv      id-automorphism = id
  Category.Isomorphism.inverseₗ id-automorphism = Properties.identityₗ(_∘_)(id)
  Category.Isomorphism.inverseᵣ id-automorphism = Properties.identityᵣ(_∘_)(id)

  inverse-isomorphism : ∀{x y : Obj} → (f : x ⟶ y) → ⦃ _ : Isomorphism(f) ⦄ → Isomorphism(inv f)
  Category.Isomorphism.inv      (inverse-isomorphism f) = f
  Category.Isomorphism.inverseₗ (inverse-isomorphism f) = inverseᵣ(f)
  Category.Isomorphism.inverseᵣ (inverse-isomorphism f) = inverseₗ(f)

  module _ ⦃ [∘]-op : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z}) ⦄ where
    op-closed-under-isomorphism : ∀{A B C : Obj} → (f : B ⟶ C) → (g : A ⟶ B) → ⦃ _ : Isomorphism(f) ⦄ → ⦃ _ : Isomorphism(g) ⦄ → Isomorphism(f ∘ g)
    Category.Isomorphism.inv      (op-closed-under-isomorphism f g) = inv g ∘ inv f
    Category.Isomorphism.inverseₗ (op-closed-under-isomorphism f g) =
      symmetry(_≡_) (Category.associativity(C))
      🝖 [≡]-with(_∘ g) ⦃ BinaryOperator.left([∘]-op) ⦄ (
        Category.associativity(C)
        🝖 [≡]-with(inv g ∘_) ⦃ BinaryOperator.right([∘]-op) ⦄ (inverseₗ(f))
        🝖 Properties.identityᵣ(_∘_)(id)
      )
      🝖 inverseₗ(g)
    Category.Isomorphism.inverseᵣ (op-closed-under-isomorphism f g) =
      symmetry(_≡_) (Category.associativity(C))
      🝖 [≡]-with(_∘ inv f) ⦃ BinaryOperator.left([∘]-op) ⦄ (
        Category.associativity(C)
        🝖 [≡]-with(f ∘_) ⦃ BinaryOperator.right([∘]-op) ⦄ (inverseᵣ(g))
        🝖 Properties.identityᵣ(_∘_)(id)
      )
      🝖 inverseᵣ(f)

  instance
    Isomorphic-reflexivity : Reflexivity(Isomorphic)
    ∃.witness (Reflexivity.proof Isomorphic-reflexivity) = id
    ∃.proof   (Reflexivity.proof Isomorphic-reflexivity) = id-automorphism

  instance
    Isomorphic-symmetry : Symmetry(Isomorphic)
    ∃.witness (Symmetry.proof Isomorphic-symmetry iso-xy) = inv(∃.witness iso-xy)
    ∃.proof   (Symmetry.proof Isomorphic-symmetry iso-xy) = inverse-isomorphism(∃.witness iso-xy)

  module _ ⦃ [∘]-op : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z}) ⦄ where
    instance
      Isomorphic-transitivity : Transitivity(Isomorphic)
      ∃.witness (Transitivity.proof Isomorphic-transitivity ([∃]-intro xy) ([∃]-intro yz)) = yz ∘ xy
      ∃.proof   (Transitivity.proof Isomorphic-transitivity ([∃]-intro xy) ([∃]-intro yz)) = op-closed-under-isomorphism ⦃ [∘]-op ⦄ yz xy

    instance
      Isomorphic-equivalence : Equivalence(Isomorphic)
      Isomorphic-equivalence = record{}
