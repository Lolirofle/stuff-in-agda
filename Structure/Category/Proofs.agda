-- TODO: Generalize and move to Structure.Categorical.Proofs
module Structure.Category.Proofs where

import      Lvl
open import Data
open import Data.Tuple as Tuple using (_,_)
open import Functional using (const ; swap ; _$_)
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Category
open import Structure.Categorical.Names
open import Structure.Categorical.Properties
import      Structure.Operator.Properties as Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Syntax.Transitivity
open import Type

module _
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄
  (cat : Category(Morphism))
  where

  open Category(cat)
  open Category.ArrowNotation(cat)
  open Morphism.OperModule(\{x} → _∘_ {x})
  open Morphism.IdModule(\{x} → _∘_ {x})(id)
  private open module [≡]-Equivalence {x}{y} = Equivalence (Equiv-equivalence ⦃ morphism-equiv{x}{y} ⦄) using ()

  private variable x y z : Obj
  private variable f g h i : x ⟶ y

  associate4-123-321 : (((f ∘ g) ∘ h) ∘ i ≡ f ∘ (g ∘ (h ∘ i)))
  associate4-123-321 = Morphism.associativity(_∘_) 🝖 Morphism.associativity(_∘_)

  associate4-123-213 : (((f ∘ g) ∘ h) ∘ i ≡ (f ∘ (g ∘ h)) ∘ i)
  associate4-123-213 = congruence₂-₁(_∘_)(_) (Morphism.associativity(_∘_))

  associate4-321-231 : (f ∘ (g ∘ (h ∘ i)) ≡ f ∘ ((g ∘ h) ∘ i))
  associate4-321-231 = congruence₂-₂(_∘_)(_) (symmetry(_≡_) (Morphism.associativity(_∘_)))

  associate4-213-121 : ((f ∘ (g ∘ h)) ∘ i ≡ (f ∘ g) ∘ (h ∘ i))
  associate4-213-121 = symmetry(_≡_) (congruence₂-₁(_∘_)(_) (Morphism.associativity(_∘_))) 🝖 Morphism.associativity(_∘_)

  associate4-231-213 : f ∘ ((g ∘ h) ∘ i) ≡ (f ∘ (g ∘ h)) ∘ i
  associate4-231-213 = symmetry(_≡_) (Morphism.associativity(_∘_))

  associate4-231-123 : f ∘ ((g ∘ h) ∘ i) ≡ ((f ∘ g) ∘ h) ∘ i
  associate4-231-123 = associate4-231-213 🝖 symmetry(_≡_) associate4-123-213

  associate4-231-121 : (f ∘ ((g ∘ h) ∘ i) ≡ (f ∘ g) ∘ (h ∘ i))
  associate4-231-121 = congruence₂-₂(_∘_)(_) (Morphism.associativity(_∘_)) 🝖 symmetry(_≡_) (Morphism.associativity(_∘_))

  associate4-321-213 : (f ∘ (g ∘ (h ∘ i)) ≡ (f ∘ (g ∘ h)) ∘ i)
  associate4-321-213 = associate4-321-231 🝖 associate4-231-213

  id-automorphism : Automorphism(id{x})
  ∃.witness id-automorphism = id
  ∃.proof   id-automorphism = intro(Morphism.identityₗ(_∘_)(id)) , intro(Morphism.identityᵣ(_∘_)(id))

  inverse-isomorphism : (f : x ⟶ y) → ⦃ _ : Isomorphism(f) ⦄ → Isomorphism(inv f)
  ∃.witness (inverse-isomorphism f) = f
  ∃.proof   (inverse-isomorphism f) = intro (inverseᵣ(f)(inv f)) , intro (inverseₗ(f)(inv f)) where
    open Isomorphism(f)

  module _ ⦃ op : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z}) ⦄ where
    op-closed-under-isomorphism : ∀{A B C : Obj} → (f : B ⟶ C) → (g : A ⟶ B) → ⦃ _ : Isomorphism(f) ⦄ → ⦃ _ : Isomorphism(g) ⦄ → Isomorphism(f ∘ g)
    ∃.witness (op-closed-under-isomorphism f g) = inv g ∘ inv f
    Tuple.left (∃.proof (op-closed-under-isomorphism f g)) = intro $
      (inv g ∘ inv f) ∘ (f ∘ g) 🝖-[ associate4-213-121 ]-sym
      (inv g ∘ (inv f ∘ f)) ∘ g 🝖-[ congruence₂-₁(_∘_) ⦃ op ⦄ (g) (congruence₂-₂(_∘_) ⦃ op ⦄ (inv g) (Morphism.inverseₗ(_∘_)(id) (f)(inv f))) ]
      (inv g ∘ id) ∘ g          🝖-[ congruence₂-₁(_∘_) ⦃ op ⦄ (g) (Morphism.identityᵣ(_∘_)(id)) ]
      inv g ∘ g                 🝖-[ Morphism.inverseₗ(_∘_)(id) (g)(inv g) ]
      id                        🝖-end
      where
        open Isomorphism(f)
        open Isomorphism(g)
    Tuple.right (∃.proof (op-closed-under-isomorphism f g)) = intro $
      (f ∘ g) ∘ (inv g ∘ inv f) 🝖-[ associate4-213-121 ]-sym
      (f ∘ (g ∘ inv g)) ∘ inv f 🝖-[ congruence₂-₁(_∘_) ⦃ op ⦄ (_) (congruence₂-₂(_∘_) ⦃ op ⦄ (_) (Morphism.inverseᵣ(_∘_)(id) (_)(_))) ]
      (f ∘ id) ∘ inv f          🝖-[ congruence₂-₁(_∘_) ⦃ op ⦄ (_) (Morphism.identityᵣ(_∘_)(id)) ]
      f ∘ inv f                 🝖-[ Morphism.inverseᵣ(_∘_)(id) (_)(_) ]
      id                        🝖-end
      where
        open Isomorphism(f)
        open Isomorphism(g)

  instance
    Isomorphic-reflexivity : Reflexivity(Isomorphic)
    Isomorphic-reflexivity = intro(Isomorphic.intro-by-isomorphism id-automorphism)

  instance
    Isomorphic-symmetry : Symmetry(Isomorphic)
    Isomorphic-symmetry = intro \iso → Isomorphic.intro-by-isomorphism (inverse-isomorphism _ ⦃ Isomorphic.isomorphismRight iso ⦄)

  module _ ⦃ op : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z}) ⦄ where
    instance
      Isomorphic-transitivity : Transitivity(Isomorphic)
      Isomorphic-transitivity = intro \iso-xy iso-yz → Isomorphic.intro-by-isomorphism $
        op-closed-under-isomorphism ⦃ op ⦄ _ _
          ⦃ Isomorphic.isomorphismRight iso-yz ⦄
          ⦃ Isomorphic.isomorphismRight iso-xy ⦄

    instance
      Isomorphic-equivalence : Equivalence(Isomorphic)
      Isomorphic-equivalence = record{}
