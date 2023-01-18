open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Classical.Semantics.Homomorphism (𝔏 : Signature) where
open Signature(𝔏)

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.ListSized
open import Data.ListSized.Functions
open import Formalization.PredicateLogic.Classical.Semantics(𝔏)
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; _←_)
open import Logic.Propositional as Logic using (_↔_)
import      Logic.Predicate     as Logic
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet)
open        Sets.PredicateSet.BoundedQuantifiers
open import Structure.Function.Domain
open import Syntax.Function
open import Type.Dependent.Sigma renaming (intro to _,_)
open import Type.Properties.Decidable
open import Type

private variable ℓ ℓₘ ℓₘ₁ ℓₘ₂ ℓₑ : Lvl.Level
private variable P : Type{ℓₚ}
private variable args n vars : ℕ
private variable 𝔐 : Model

private variable A B C S : Model{ℓₘ}
private variable fi : Obj n
private variable ri : Prop n
private variable xs : List(dom(S))(n)

record Homomorphism (A : Model{ℓₘ₁}) (B : Model{ℓₘ₂}) (f : dom(A) → dom(B)) : Type{ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ Lvl.of(Type.of A) Lvl.⊔ Lvl.of(Type.of B)} where
  field
    preserve-functions : ∀{xs} → (f(fn(A) fi xs) ≡ fn(B) fi (map f xs))
    preserve-relations : ∀{xs} → IsTrue(rel(A) ri xs) → IsTrue(rel(B) ri (map f xs))

_→ₛₜᵣᵤ_ : Model{ℓₘ₁} → Model{ℓₘ₂} → Type
A →ₛₜᵣᵤ B = Logic.∃(Homomorphism A B)

record Embedding (A : Model{ℓₘ₁}) (B : Model{ℓₘ₂}) (f : dom(A) → dom(B)) : Type{ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ Lvl.of(Type.of A) Lvl.⊔ Lvl.of(Type.of B)} where
  constructor intro
  field
    ⦃ homomorphism ⦄ : Homomorphism(A)(B)(f)
    ⦃ injection ⦄    : Injective(f)
    preserve-relations-converse : ∀{xs} → IsTrue(rel(A) ri xs) ← IsTrue(rel(B) ri (map f xs))

open import Data
open import Data.Boolean.Stmt
open import Data.ListSized.Proofs
open import Functional
open import Function.Equals
open import Function.Proofs
open import Functional.Instance
open import Logic.Predicate
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity

idₛₜᵣᵤ : A →ₛₜᵣᵤ A
∃.witness idₛₜᵣᵤ = id
Homomorphism.preserve-functions (∃.proof (idₛₜᵣᵤ {A = A})) {n} {fi} {xs} = congruence₁(fn A fi) (symmetry(_≡_) (_⊜_.proof map-id))
Homomorphism.preserve-relations (∃.proof (idₛₜᵣᵤ {A = A})) {n} {ri} {xs} = substitute₁ₗ(IsTrue ∘ rel A ri) (_⊜_.proof map-id)

_∘ₛₜᵣᵤ_ : let _ = A ; _ = B ; _ = C in (B →ₛₜᵣᵤ C) → (A →ₛₜᵣᵤ B) → (A →ₛₜᵣᵤ C)
∃.witness (([∃]-intro f) ∘ₛₜᵣᵤ ([∃]-intro g)) = f ∘ g
Homomorphism.preserve-functions (∃.proof (_∘ₛₜᵣᵤ_ {A = A} {B = B} {C = C} ([∃]-intro f ⦃ hom-f ⦄) ([∃]-intro g ⦃ hom-g ⦄))) {fi = fi} {xs} =
  congruence₁(f) (Homomorphism.preserve-functions hom-g)
  🝖 Homomorphism.preserve-functions hom-f
  🝖 congruence₁(fn C fi) (symmetry(_≡_) (_⊜_.proof (map-[∘] {f = f}{g = g}) {xs}))
Homomorphism.preserve-relations (∃.proof (_∘ₛₜᵣᵤ_ {A = A} {B = B} {C = C} ([∃]-intro f ⦃ hom-f ⦄) ([∃]-intro g ⦃ hom-g ⦄))) {ri = ri} {xs} =
  substitute₁ₗ(IsTrue ∘ rel C ri) (_⊜_.proof map-[∘] {xs})
  ∘ Homomorphism.preserve-relations hom-f
  ∘ Homomorphism.preserve-relations hom-g

import      Data.Tuple as Tuple
open import Function.Equals
open import Function.Equals.Proofs
open import Function.Inverse
open import Lang.Inspect
open import Logic.Predicate.Equiv
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Function.Domain.Proofs

instance
  map-function : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → Function ⦃ [⊜]-equiv ⦄ ⦃ [⊜]-equiv ⦄ (map{A = A}{B = B}{n = n})
  map-function {A = A}{B = B} = intro proof where
    proof : ∀{f g : A → B} → (f ⊜ g) → (map{n = n} f ⊜ map g)
    _⊜_.proof (proof p) {∅}     = reflexivity(_≡_)
    _⊜_.proof (proof p) {x ⊰ l} = congruence₂(_⊰_) (_⊜_.proof p) (_⊜_.proof (proof p) {l})

instance
  Structure-Homomorphism-category : Category(_→ₛₜᵣᵤ_ {ℓₘ})
  Category._∘_ Structure-Homomorphism-category = _∘ₛₜᵣᵤ_
  Category.id  Structure-Homomorphism-category = idₛₜᵣᵤ
  BinaryOperator.congruence (Category.binaryOperator Structure-Homomorphism-category) = [⊜][∘]-binaryOperator-raw
  _⊜_.proof (Morphism.Associativity.proof (Category.associativity Structure-Homomorphism-category) {_} {_} {_} {_} {[∃]-intro f} {[∃]-intro g} {[∃]-intro h}) {x} = reflexivity(_≡_) {f(g(h(x)))}
  _⊜_.proof (Morphism.Identityₗ.proof (Tuple.left (Category.identity Structure-Homomorphism-category)) {f = [∃]-intro f}) {x} = reflexivity(_≡_) {f(x)}
  _⊜_.proof (Morphism.Identityᵣ.proof (Tuple.right (Category.identity Structure-Homomorphism-category)) {f = [∃]-intro f}) {x} = reflexivity(_≡_) {f(x)}

module _ {F@([∃]-intro f) : _→ₛₜᵣᵤ_ {ℓₘ}{ℓₘ} A B} where
  isomorphism-surjective-embedding : Morphism.Isomorphism ⦃ [≡∃]-equiv ⦃ [⊜]-equiv ⦄ ⦄ (\{A} → _∘ₛₜᵣᵤ_ {A = A})(idₛₜᵣᵤ)(F) ↔ (Surjective(f) Logic.∧ Embedding(A)(B)(f))
  Tuple.left isomorphism-surjective-embedding (Logic.[∧]-intro surj embed) = [∃]-intro ([∃]-intro _ ⦃ hom ⦄) ⦃ Logic.[∧]-intro inverₗ inverᵣ ⦄ where
    f⁻¹ = invᵣ-surjective f ⦃ surj ⦄
    instance
      inver : Inverse(f)(f⁻¹)
      inver = Logic.[∧]-elimᵣ ([∃]-proof (bijective-to-invertible ⦃ bij = injective-surjective-to-bijective(f)  ⦃ Embedding.injection embed ⦄ ⦃ surj ⦄ ⦄))

    instance
      hom : Homomorphism(B)(A)(f⁻¹)
      Homomorphism.preserve-functions hom {fi = fi} {xs = xs} =
        f⁻¹(fn B fi xs)                   🝖[ _≡_ ]-[ congruence₁(f⁻¹) (congruence₁(fn B fi) (_⊜_.proof map-id)) ]-sym
        f⁻¹(fn B fi (map id xs))          🝖[ _≡_ ]-[ congruence₁(f⁻¹) (congruence₁(fn B fi) (_⊜_.proof (congruence₁(map) (intro (Inverseᵣ.proof(Logic.[∧]-elimᵣ inver)))) {xs})) ]-sym
        f⁻¹(fn B fi (map (f ∘ f⁻¹) xs))   🝖[ _≡_ ]-[ congruence₁(f⁻¹) (congruence₁(fn B fi) (_⊜_.proof map-[∘] {xs})) ]
        f⁻¹(fn B fi (map f (map f⁻¹ xs))) 🝖[ _≡_ ]-[ congruence₁(f⁻¹) (Homomorphism.preserve-functions (Embedding.homomorphism embed)) ]-sym
        f⁻¹(f(fn A fi (map f⁻¹ xs)))      🝖[ _≡_ ]-[ Inverseₗ.proof(Logic.[∧]-elimₗ inver) ]
        fn A fi (map f⁻¹ xs)              🝖-end

      Homomorphism.preserve-relations hom {ri = ri} {xs = xs} p = Embedding.preserve-relations-converse embed {xs = map f⁻¹ xs} (substitute₁ᵣ(IsTrue ∘ rel B ri) (_⊜_.proof proof {xs}) p) where
        proof =
          id                🝖[ _⊜_ ]-[ map-id ]-sym
          map id            🝖[ _⊜_ ]-[ congruence₁(map) (intro (Inverseᵣ.proof(Logic.[∧]-elimᵣ inver))) ]-sym
          map(f ∘ f⁻¹)      🝖[ _⊜_ ]-[ map-[∘] ]
          (map f ∘ map f⁻¹) 🝖-end

    inverₗ : Morphism.Inverseₗ _ _ F ([∃]-intro f⁻¹)
    Morphism.Inverseₗ.proof inverₗ = intro(Inverseₗ.proof(Logic.[∧]-elimₗ inver))

    inverᵣ : Morphism.Inverseᵣ _ _ F ([∃]-intro f⁻¹)
    Morphism.Inverseᵣ.proof inverᵣ = intro(Inverseᵣ.proof(Logic.[∧]-elimᵣ inver))
  Tuple.right isomorphism-surjective-embedding iso = Logic.[∧]-intro infer (intro (\{n}{ri}{xs} → {!proof!})) where
    instance
      bij : Bijective(f)
    instance
      inj : Injective(f)
      inj = bijective-to-injective(f)
    instance
      surj : Surjective(f)
      surj = bijective-to-surjective(f)
    proof : IsTrue(rel A ri xs) ← IsTrue(rel B ri (map f(xs)))
    proof p relation x = {!!}
    proof2 : let _ = (rel A ri xs) in Surjective(f)
    proof2 = {!!}
-- (intro (proof {!!} {!!}))
