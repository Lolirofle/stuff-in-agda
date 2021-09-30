module Structure.Signature where

open import Data.Tuple.Raise
open import Data.Tuple.Raiseᵣ.Functions
import      Lvl
open import Numeral.Natural
open import Structure.Function
open import Structure.Setoid
open import Structure.Relator
open import Type

private variable ℓ ℓᵢ ℓᵢ₁ ℓᵢ₂ ℓᵢ₃ ℓd ℓd₁ ℓd₂ ℓᵣ ℓᵣ₁ ℓᵣ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable n : ℕ

-- A signature consists of a family of sets of function and relation symbols over a set.
-- `functions(n)` and `relations(n)` should be interpreted as the indices for functions/relations of arity `n`.
record Signature : Type{Lvl.𝐒(ℓᵢ₁ Lvl.⊔ ℓᵢ₂)} where
  field
    functions : ℕ → Type{ℓᵢ₁}
    relations : ℕ → Type{ℓᵢ₂}

private variable s : Signature{ℓᵢ₁}{ℓᵢ₂}

import      Data.Tuple.Equiv as Tuple

-- A structure with a signature `s` consists of a domain and interpretations of the function/relation symbols in `s`.
record Structure (s : Signature{ℓᵢ₁}{ℓᵢ₂}) : Type{Lvl.𝐒(ℓₑ Lvl.⊔ ℓd Lvl.⊔ ℓᵣ) Lvl.⊔ ℓᵢ₁ Lvl.⊔ ℓᵢ₂} where
  open Signature(s)
  field
    domain : Type{ℓd}
    ⦃ equiv ⦄ : ∀{n} → Equiv{ℓₑ}(domain ^ n)
    ⦃ ext ⦄ : ∀{n} → Tuple.Extensionality(equiv{𝐒(𝐒 n)})
    function : functions(n) → ((domain ^ n) → domain)
    ⦃ function-func ⦄ : ∀{fi} → Function(function{n} fi)
    relation : relations(n) → ((domain ^ n) → Type{ℓᵣ})
    ⦃ relation-func ⦄ : ∀{ri} → UnaryRelator(relation{n} ri)

open Structure public using() renaming (domain to dom ; function to fn ; relation to rel)

open import Logic.Predicate

module _ {s : Signature{ℓᵢ₁}{ℓᵢ₂}} where
  private variable A B C S : Structure{ℓd = ℓd}{ℓᵣ = ℓᵣ}(s)
  private variable fi : Signature.functions s n
  private variable ri : Signature.relations s n
  private variable xs : dom(S) ^ n

  record Homomorphism
    (A : Structure{ℓₑ = ℓₑ₁}{ℓd = ℓd₁}{ℓᵣ = ℓᵣ₁}(s))
    (B : Structure{ℓₑ = ℓₑ₂}{ℓd = ℓd₂}{ℓᵣ = ℓᵣ₂}(s))
    (f : dom(A) → dom(B))
    : Type{ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓd₁ Lvl.⊔ ℓd₂ Lvl.⊔ ℓᵣ₁ Lvl.⊔ ℓᵣ₂ Lvl.⊔ Lvl.ofType(Type.of s)}
    where
  
    field
      ⦃ function ⦄ : Function(f)
      preserve-functions : ∀{xs : dom(A) ^ n} → (f(fn(A) fi xs) ≡ fn(B) fi (map f xs))
      preserve-relations : ∀{xs : dom(A) ^ n} → (rel(A) ri xs) → (rel(B) ri (map f xs))

  _→ₛₜᵣᵤ_ : Structure{ℓₑ = ℓₑ₁}{ℓd = ℓd₁}{ℓᵣ = ℓᵣ₁}(s) → Structure{ℓₑ = ℓₑ₂}{ℓd = ℓd₂}{ℓᵣ = ℓᵣ₂}(s) → Type
  A →ₛₜᵣᵤ B = ∃(Homomorphism A B)

  open import Data
  open import Data.Tuple as Tuple using (_,_)
  open import Data.Tuple.Raiseᵣ.Proofs
  open import Functional
  open import Function.Proofs
  open import Lang.Instance
  open import Structure.Operator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  idₛₜᵣᵤ : A →ₛₜᵣᵤ A
  ∃.witness idₛₜᵣᵤ = id
  Homomorphism.preserve-functions (∃.proof (idₛₜᵣᵤ {A = A})) {n} {fi} {xs} = congruence₁(fn A fi) (symmetry(Equiv._≡_ (Structure.equiv A)) ⦃ Equiv.symmetry infer ⦄ map-id)
  Homomorphism.preserve-relations (∃.proof (idₛₜᵣᵤ {A = A})) {n} {ri} {xs} = substitute₁ₗ(rel A ri) map-id

  _∘ₛₜᵣᵤ_ : let _ = A , B , C in (B →ₛₜᵣᵤ C) → (A →ₛₜᵣᵤ B) → (A →ₛₜᵣᵤ C)
  ∃.witness (([∃]-intro f) ∘ₛₜᵣᵤ ([∃]-intro g)) = f ∘ g
  Homomorphism.function (∃.proof ([∃]-intro f ∘ₛₜᵣᵤ [∃]-intro g)) = [∘]-function {f = f}{g = g}
  Homomorphism.preserve-functions (∃.proof (_∘ₛₜᵣᵤ_ {A = A} {B = B} {C = C} ([∃]-intro f ⦃ hom-f ⦄) ([∃]-intro g ⦃ hom-g ⦄))) {fi = fi} = transitivity(_≡_) ⦃ Equiv.transitivity infer ⦄ (transitivity(_≡_) ⦃ Equiv.transitivity infer ⦄ (congruence₁(f) (Homomorphism.preserve-functions hom-g)) (Homomorphism.preserve-functions hom-f)) (congruence₁(fn C fi) (symmetry(Equiv._≡_ (Structure.equiv C)) ⦃ Equiv.symmetry infer ⦄ (map-[∘] {f = f}{g = g})))
  Homomorphism.preserve-relations (∃.proof (_∘ₛₜᵣᵤ_ {A = A} {B = B} {C = C} ([∃]-intro f ⦃ hom-f ⦄) ([∃]-intro g ⦃ hom-g ⦄))) {ri = ri} = substitute₁ₗ (rel C ri) map-[∘] ∘ Homomorphism.preserve-relations hom-f ∘ Homomorphism.preserve-relations hom-g

  open import Function.Equals
  open import Function.Equals.Proofs
  open import Logic.Predicate.Equiv
  open import Structure.Category
  open import Structure.Categorical.Properties

  Structure-Homomorphism-category : Category(_→ₛₜᵣᵤ_ {ℓₑ}{ℓd}{ℓᵣ})
  Category._∘_ Structure-Homomorphism-category = _∘ₛₜᵣᵤ_
  Category.id  Structure-Homomorphism-category = idₛₜᵣᵤ
  BinaryOperator.congruence (Category.binaryOperator Structure-Homomorphism-category) = [⊜][∘]-binaryOperator-raw
  _⊜_.proof (Morphism.Associativity.proof (Category.associativity Structure-Homomorphism-category) {_} {_} {_} {_} {[∃]-intro f} {[∃]-intro g} {[∃]-intro h}) {x} = reflexivity(_≡_) ⦃ Equiv.reflexivity infer ⦄ {f(g(h(x)))}
  _⊜_.proof (Morphism.Identityₗ.proof (Tuple.left (Category.identity Structure-Homomorphism-category)) {f = [∃]-intro f}) {x} = reflexivity(_≡_) ⦃ Equiv.reflexivity infer ⦄ {f(x)}
  _⊜_.proof (Morphism.Identityᵣ.proof (Tuple.right (Category.identity Structure-Homomorphism-category)) {f = [∃]-intro f}) {x} = reflexivity(_≡_) ⦃ Equiv.reflexivity infer ⦄ {f(x)}

module _ (s : Signature{ℓᵢ₁}{ℓᵢ₂}) where
  data Term : Type{ℓᵢ₁} where
    var  : ℕ → Term
    func : (Signature.functions s n) → (Term ^ n) → Term
