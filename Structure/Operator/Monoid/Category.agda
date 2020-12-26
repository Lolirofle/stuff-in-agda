module Structure.Operator.Monoid.Category where

open import Data
open import Data.Tuple as Tuple using (_,_)
open import Functional
import      Lvl
open import Structure.Setoid
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Operator.Monoid
open import Structure.Operator.Monoid.Homomorphism
open import Structure.Operator.Properties using (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator
open import Type

private variable ℓ ℓₑ ℓₗ ℓₗₑ : Lvl.Level
private variable T : Type{ℓ}
private variable _▫_ : T → T → T

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ oper : BinaryOperator(_▫_) ⦄
  (M : Monoid{T = T}(_▫_))
  where

  -- A monoid as a special case of a category with a single object and morphisms in and out of this object.
  -- Composition and identity in the category is the binary operator and the identity element from the monoid.
  monoidCategory : Category{Obj = Unit{Lvl.𝟎}}(const(const(T)))
  Category._∘_            monoidCategory = (_▫_)
  Category.id             monoidCategory = Monoid.id(M)
  Category.binaryOperator monoidCategory = oper
  Category.associativity  monoidCategory = Morphism.intro(associativity(_▫_))
  Category.identity       monoidCategory = Morphism.intro (identityₗ(_▫_)(Monoid.id(M))) , Morphism.intro ((identityᵣ(_▫_)(Monoid.id(M))))

module _ where
  open import Function.Equals
  open import Function.Equals.Proofs
  open import Function.Proofs
  open import Logic.Predicate
  open import Logic.Propositional
  open import Structure.Function.Multi
  open import Structure.Function
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties
  open import Syntax.Function
  open import Syntax.Transitivity

  private variable x y z : MonoidObject{ℓₗ}{ℓₗₑ}

  instance
    [→ᵐᵒⁿᵒⁱᵈ]-equiv : Equiv(x →ᵐᵒⁿᵒⁱᵈ y)
    Equiv._≡_ [→ᵐᵒⁿᵒⁱᵈ]-equiv ([∃]-intro F) ([∃]-intro G) = F ⊜ G
    Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence [→ᵐᵒⁿᵒⁱᵈ]-equiv)) = reflexivity(_⊜_)
    Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence [→ᵐᵒⁿᵒⁱᵈ]-equiv)) = symmetry(_⊜_)
    Transitivity.proof (Equivalence.transitivity (Equiv.equivalence [→ᵐᵒⁿᵒⁱᵈ]-equiv)) = transitivity(_⊜_)

  -- Identity monoid homomorphism.
  idᵐᵒⁿᵒⁱᵈ : x →ᵐᵒⁿᵒⁱᵈ x
  ∃.witness idᵐᵒⁿᵒⁱᵈ = id
  Homomorphism.function                      (∃.proof idᵐᵒⁿᵒⁱᵈ)  = id-function
  Preserving.proof (Homomorphism.preserve-op (∃.proof idᵐᵒⁿᵒⁱᵈ)) = reflexivity(_≡_)
  Preserving.proof (Homomorphism.preserve-id (∃.proof idᵐᵒⁿᵒⁱᵈ)) = reflexivity(_≡_)

  -- Composition of monoid homomorphisms.
  _∘ᵐᵒⁿᵒⁱᵈ_ : let _ = x in (y →ᵐᵒⁿᵒⁱᵈ z) → (x →ᵐᵒⁿᵒⁱᵈ y) → (x →ᵐᵒⁿᵒⁱᵈ z)
  ∃.witness (([∃]-intro F) ∘ᵐᵒⁿᵒⁱᵈ ([∃]-intro G)) = F ∘ G
  Homomorphism.function                      (∃.proof (([∃]-intro F) ∘ᵐᵒⁿᵒⁱᵈ ([∃]-intro G)))  = [∘]-function {f = F}{g = G}
  Preserving.proof (Homomorphism.preserve-op (∃.proof (_∘ᵐᵒⁿᵒⁱᵈ_ {x = A} {y = B} {z = C} ([∃]-intro F) ([∃]-intro G)))) {x} {y} =
    (F ∘ G)(x ⦗ MonoidObject._▫_ A ⦘ y)          🝖[ _≡_ ]-[]
    F(G(x ⦗ MonoidObject._▫_ A ⦘ y))             🝖[ _≡_ ]-[ congruence₁(F) (preserving₂(G) (MonoidObject._▫_ A) (MonoidObject._▫_ B)) ]
    F(G(x) ⦗ MonoidObject._▫_ B ⦘ G(y))          🝖[ _≡_ ]-[ preserving₂(F) (MonoidObject._▫_ B) (MonoidObject._▫_ C) ]
    F(G(x)) ⦗ MonoidObject._▫_ C ⦘ F(G(y))       🝖[ _≡_ ]-[]
    (F ∘ G)(x) ⦗ MonoidObject._▫_ C ⦘ (F ∘ G)(y) 🝖-end
  Preserving.proof (Homomorphism.preserve-id (∃.proof (_∘ᵐᵒⁿᵒⁱᵈ_ {x = A} {y = B} {z = C} ([∃]-intro F) ([∃]-intro G)))) =
    (F ∘ G)(MonoidObject.id A) 🝖[ _≡_ ]-[]
    F(G(MonoidObject.id A))    🝖[ _≡_ ]-[ congruence₁(F) (preserving₀(G) (MonoidObject.id A) (MonoidObject.id B)) ]
    F(MonoidObject.id B)       🝖[ _≡_ ]-[ preserving₀(F) (MonoidObject.id B) (MonoidObject.id C) ]
    MonoidObject.id C          🝖-end

  -- A category where the objects are monoids themselves and the morphisms are homomorphism between them.
  instance
    monoidObjectCategory : Category{Obj = MonoidObject{ℓₗ}{ℓₗₑ}}(_→ᵐᵒⁿᵒⁱᵈ_)
    Category._∘_            monoidObjectCategory = _∘ᵐᵒⁿᵒⁱᵈ_
    Category.id             monoidObjectCategory = idᵐᵒⁿᵒⁱᵈ
    Category.binaryOperator monoidObjectCategory = intro(\p q → [⊜][∘]-binaryOperator-raw p q)
    Category.associativity  monoidObjectCategory = Morphism.intro (reflexivity(_⊜_))
    Category.identity       monoidObjectCategory = [∧]-intro (Morphism.intro(reflexivity(_⊜_))) (Morphism.intro(reflexivity(_⊜_)))

  monoidObjectCategoryObject : ∀{ℓₗ ℓₑ} → CategoryObject
  monoidObjectCategoryObject{ℓₗ}{ℓₑ} = intro(monoidObjectCategory{ℓₗ}{ℓₑ})
