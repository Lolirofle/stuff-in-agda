module Sets.ExtensionalPredicateSet where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Function.Equals
open import Function.Equals.Proofs
open import Function.Inverse
open import Function.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems using (contrapositiveᵣ) renaming ([↔]-transitivity to [↔]-transitivity-raw)
open import Logic.Predicate
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Function
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Relator.Proofs
open import Structure.Relator
open import Syntax.Transitivity
open import Type
open import Type.Size

private variable ℓ ℓₒ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level
private variable T A A₁ A₂ B : Type{ℓ}

-- A set of objects of a certain type where equality is based on setoids.
-- This is defined by the containment predicate (_∋_) and a proof that it respects the setoid structure.
-- (A ∋ a) is read "The set A contains the element a".
-- Note: This is only a "set" within a certain type, so a collection of type PredSet(T) is actually a subcollection of T.
record PredSet {ℓ ℓₒ ℓₑ} (T : Type{ℓₒ}) ⦃ equiv : Equiv{ℓₑ}(T) ⦄ : Type{Lvl.𝐒(ℓ) Lvl.⊔ ℓₒ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    _∋_ : T → Stmt{ℓ}
    ⦃ preserve-equiv ⦄ : UnaryRelator(_∋_)
open PredSet using (_∋_) public
open PredSet using (preserve-equiv)

-- Element-set relations.
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  -- The membership relation.
  -- (a ∈ A) is read "The element a is included in the set A".
  _∈_ : T → PredSet{ℓ}(T) → Stmt
  _∈_ = swap(_∋_)

  _∉_ : T → PredSet{ℓ}(T) → Stmt
  _∉_ = (¬_) ∘₂ (_∈_)

  _∌_ : PredSet{ℓ}(T) → T → Stmt
  _∌_ = (¬_) ∘₂ (_∋_)

  NonEmpty : PredSet{ℓ}(T) → Stmt
  NonEmpty(S) = ∃(_∈ S)

-- Set-bounded quantifiers.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  ∀ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ Lvl.⊔ ℓ₁ Lvl.⊔ ℓₒ}
  ∀ₛ(S) P = ∀{elem : T} → (elem ∈ S) → P(elem)

  ∃ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ Lvl.⊔ ℓ₁ Lvl.⊔ ℓₒ}
  ∃ₛ(S) P = ∃(elem ↦ (elem ∈ S) ∧ P(elem))

-- Sets and set operations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  -- An empty set.
  -- Contains nothing.
  ∅ : PredSet{ℓ}(T)
  ∅ ∋ x = Empty
  preserve-equiv ∅ = UnaryRelator-introᵣ(const id)

  -- An universal set.
  -- Contains everything.
  -- Note: Everything as in every object of type  T.
  𝐔 : PredSet{ℓ}(T)
  𝐔 ∋ x = Unit
  preserve-equiv 𝐔 = UnaryRelator-introᵣ(const id)

  -- A singleton set (a set containing only one element).
  •_ : T → PredSet(T)
  (• a) ∋ x = x ≡ₑ a
  preserve-equiv (• a) = UnaryRelator-introᵣ \xy xa → symmetry(_≡ₑ_) xy 🝖 xa

  -- An union of two sets.
  -- Contains the elements that any of the both sets contain.
  _∪_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  (A ∪ B) ∋ x = (A ∋ x) ∨ (B ∋ x)
  preserve-equiv (A ∪ B) = UnaryRelator-introᵣ \xy → Either.map (substitute₁ᵣ(A ∋_) xy) (substitute₁ᵣ(B ∋_) xy)
  infixr 1000 _∪_

  -- An intersection of two sets.
  -- Contains the elements that both of the both sets contain.
  _∩_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  (A ∩ B) ∋ x = (A ∋ x) ∧ (B ∋ x)
  preserve-equiv (A ∩ B) = UnaryRelator-introᵣ \xy → Tuple.map (substitute₁ᵣ(A ∋_) xy) (substitute₁ᵣ(B ∋_) xy)
  infixr 1001 _∩_

  -- A complement of a set.
  -- Contains the elements that the set does not contain.
  ∁_ : PredSet{ℓ}(T) → PredSet(T)
  (∁ A) ∋ x = A ∌ x
  preserve-equiv (∁ A) = UnaryRelator-introᵣ \xy → contrapositiveᵣ(substitute₁ᵣ(A ∋_) (symmetry(_≡ₑ_) xy))
  infixr 1002 ∁_

  -- A relative complement of a set.
  -- Contains the elements that the left set contains without the elements included in the right set..
  _∖_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  A ∖ B = (A ∩ (∁ B))
  infixr 1001 _∖_

  filter : (P : T → Stmt{ℓ₁}) ⦃ _ : UnaryRelator(P) ⦄ → PredSet{ℓ₂}(T) → PredSet(T)
  filter P(A) ∋ x = (x ∈ A) ∧ P(x)
  preserve-equiv (filter P A) = UnaryRelator-introᵣ \xy ([∧]-intro xA Px) → [∧]-intro (substitute₁ᵣ(A ∋_) xy xA) (substitute₁ᵣ(P) xy Px)

unapply : ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) ⦃ func-f : Function(f) ⦄ → B → PredSet(A)
unapply f(y) ∋ x = f(x) ≡ₑ y
preserve-equiv (unapply f(y)) = [∘]-unaryRelator ⦃ rel = BinaryRelator.unary₁ _ [≡]-binaryRelator ⦄

⊶ : ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) → PredSet(B)
⊶ f ∋ y = ∃(x ↦ f(x) ≡ₑ y)
preserve-equiv (⊶ f) = [∃]-unaryRelator ⦃ rel-P = BinaryRelator.unary₂ _ [≡]-binaryRelator ⦄

unmap : ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) ⦃ _ : Function(f) ⦄ → PredSet{ℓ}(B) → PredSet(A)
(unmap f(Y)) ∋ x = f(x) ∈ Y
preserve-equiv (unmap f x) = [∘]-unaryRelator{f = f}

map : ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) → PredSet{ℓ}(A) → PredSet(B)
map f(S) ∋ y = ∃(x ↦ (x ∈ S) ∧ (f(x) ≡ₑ y))
preserve-equiv (map f S) = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-Q = BinaryRelator.unary₂ _ [≡]-binaryRelator ⦄ ⦄

map₂ : ⦃ _ : Equiv{ℓₑ₁}(A₁) ⦄ ⦃ _ : Equiv{ℓₑ₂}(A₂) ⦄ ⦃ _ : Equiv{ℓₑ₃}(B) ⦄ → (_▫_ : A₁ → A₂ → B) → PredSet{ℓ₁}(A₁) → PredSet{ℓ₂}(A₂) → PredSet(B)
map₂(_▫_) S₁ S₂ ∋ y = ∃{Obj = _ ⨯ _}(\{(x₁ , x₂) → (x₁ ∈ S₁) ∧ (x₂ ∈ S₂) ∧ ((x₁ ▫ x₂) ≡ₑ y)})
preserve-equiv (map₂ (_▫_) S₁ S₂) = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦄ ⦃ rel-Q = BinaryRelator.unary₂ _ [≡]-binaryRelator ⦄ ⦄

-- Set-set relations.
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  record _⊆_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{Lvl.of(T) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) → (x ∈ B)

  record _⊇_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{Lvl.of(T) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ← (x ∈ B)

  record _≡_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{Lvl.of(T) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ↔ (x ∈ B)

  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    Reflexivity.proof [≡]-reflexivity = intro(reflexivity(_↔_))

  instance
    [≡]-symmetry : Symmetry(_≡_ {ℓ})
    Symmetry.proof [≡]-symmetry (intro xy) = intro(symmetry(_↔_) xy)

  [≡]-transitivity-raw : ∀{A : PredSet{ℓ₁}(T)}{B : PredSet{ℓ₂}(T)}{C : PredSet{ℓ₃}(T)} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [≡]-transitivity-raw (intro xy) (intro yz) = intro([↔]-transitivity-raw xy yz)

  instance
    [≡]-transitivity : Transitivity(_≡_ {ℓ})
    Transitivity.proof [≡]-transitivity (intro xy) (intro yz) = intro(transitivity(_↔_) xy yz)

  instance
    [≡]-equivalence : Equivalence(_≡_ {ℓ})
    [≡]-equivalence = intro

  instance
    [≡]-equiv : Equiv(PredSet{ℓ}(T))
    Equiv._≡_ ([≡]-equiv {ℓ}) x y = x ≡ y
    Equiv.equivalence [≡]-equiv = [≡]-equivalence

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    -- Note: The purpose of this module is to satisfy this property for arbitrary equivalences.
    [∋]-binaryRelator : BinaryRelator(_∋_ {ℓ}{T = T})
    [∋]-binaryRelator = BinaryRelator-introᵣ \(intro pₛ) pₑ p → [↔]-to-[→] pₛ(substitute₁ᵣ(_) pₑ p)

  [∈]-binaryRelator : BinaryRelator(_∈_ {T = T}{ℓ})
  [∈]-binaryRelator = BinaryRelator-introᵣ \pₑ (intro pₛ) p → [↔]-to-[→] pₛ(substitute₁ᵣ(_) pₑ p)

  instance
    [∋]-unaryRelatorₗ : ∀{a : T} → UnaryRelator(A ↦ _∋_ {ℓ} A a)
    [∋]-unaryRelatorₗ = BinaryRelator.unary₁ _ [∋]-binaryRelator

-- TODO: There are level problems here that I am not sure how to solve. The big union of a set of sets are not of the same type as the inner sets. So, for example it would be useful if (⋃ As : PredSet{ℓₒ Lvl.⊔ Lvl.𝐒(ℓ₁)}(T)) and (A : PredSet{ℓ₁}(T)) for (A ∈ As) had the same type/levels when (As : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T))) so that they become comparable. But here, the result of big union have one greater level.
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  -- ⋃_ : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T)) → PredSet{ℓₒ Lvl.⊔ Lvl.𝐒(ℓ₁)}(T)
  ⋃ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  (⋃ As) ∋ x = ∃(A ↦ (A ∈ As) ∧ (x ∈ A))
  preserve-equiv (⋃ As) = UnaryRelator-introᵣ \xy → [∃]-map-proof (Tuple.mapRight (substitute₁ᵣ(_) xy))

  ⋂ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  (⋂ As) ∋ x = ∀{A} → (A ∈ As) → (x ∈ A)
  preserve-equiv (⋂ As) = UnaryRelator-introᵣ \xy p{A} → substitute₁ᵣ(_) xy ∘ p{A}

-- Indexed set operations.
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  ⋃ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ Lvl.⊔ ℓ₂}(T)
  (⋃ᵢ Ai) ∋ x = ∃(i ↦ x ∈ Ai(i))
  preserve-equiv (⋃ᵢ Ai) = UnaryRelator-introᵣ \xy → [∃]-map-proof (\{i} → substitute₁ᵣ(_) ⦃ preserve-equiv(Ai(i)) ⦄ xy)

  ⋂ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ Lvl.⊔ ℓ₂}(T)
  (⋂ᵢ Ai) ∋ x = ∀ₗ(i ↦ x ∈ Ai(i))
  preserve-equiv (⋂ᵢ Ai) = UnaryRelator-introᵣ \xy p{i} → substitute₁ᵣ(_) ⦃ preserve-equiv(Ai(i)) ⦄ xy (p{i})

  -- When the indexed union is indexed by a boolean, it is the same as the small union.
  ⋃ᵢ-of-boolean : ∀{A B : PredSet{ℓ}(T)} → ((⋃ᵢ{I = Bool}(if_then B else A)) ≡ (A ∪ B))
  ∃.witness (_⨯_.left (_≡_.proof ⋃ᵢ-of-boolean) ([∨]-introₗ p)) = 𝐹
  ∃.proof   (_⨯_.left (_≡_.proof ⋃ᵢ-of-boolean) ([∨]-introₗ p)) = p
  ∃.witness (_⨯_.left (_≡_.proof ⋃ᵢ-of-boolean) ([∨]-introᵣ p)) = 𝑇
  ∃.proof   (_⨯_.left (_≡_.proof ⋃ᵢ-of-boolean) ([∨]-introᵣ p)) = p
  _⨯_.right (_≡_.proof ⋃ᵢ-of-boolean) ([∃]-intro 𝐹 ⦃ p ⦄) = [∨]-introₗ p
  _⨯_.right (_≡_.proof ⋃ᵢ-of-boolean) ([∃]-intro 𝑇 ⦃ p ⦄) = [∨]-introᵣ p

  -- When the indexed intersection is indexed by a boolean, it is the same as the small intersection.
  ⋂ᵢ-of-boolean : ∀{A B : PredSet{ℓ}(T)} → ((⋂ᵢ{I = Bool}(if_then B else A)) ≡ (A ∩ B))
  _⨯_.left (_≡_.proof ⋂ᵢ-of-boolean) p {𝐹} = [∧]-elimₗ p
  _⨯_.left (_≡_.proof ⋂ᵢ-of-boolean) p {𝑇} = [∧]-elimᵣ p
  _⨯_.left  (_⨯_.right (_≡_.proof ⋂ᵢ-of-boolean) p) = p{𝐹}
  _⨯_.right (_⨯_.right (_≡_.proof ⋂ᵢ-of-boolean) p) = p{𝑇}

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  ⋃ᵢ-of-bijection : ∀{f : B → PredSet{ℓ}(T)} ⦃ func-f : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋃ᵢ{I = A}(f ∘ g) ≡ ⋃ᵢ{I = B}(f))
  ∃.witness (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = inv g ⦃ bijective-to-invertible ⦄ (b)
  ∃.proof (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = substitute₂ᵣ(_∋_) (symmetry(_≡_) (congruence₁(f) (inverse-right(g)(inv g ⦃ bijective-to-invertible ⦄) ⦃ [∧]-elimᵣ([∃]-proof bijective-to-invertible) ⦄))) (reflexivity(_≡ₑ_)) p
  ∃.witness (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro a ⦃ p ⦄)) = g(a)
  ∃.proof (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = p

  ⋂ᵢ-of-bijection : ∀{f : B → PredSet{ℓ}(T)} ⦃ func-f : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋂ᵢ{I = A}(f ∘ g) ≡ ⋂ᵢ{I = B}(f))
  _⨯_.left (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = p{g(b)}
  _⨯_.right (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = substitute₂ᵣ(_∋_) (congruence₁(f) (inverse-right(g)(inv g ⦃ bijective-to-invertible ⦄) ⦃ [∧]-elimᵣ([∃]-proof bijective-to-invertible) ⦄)) (reflexivity(_≡ₑ_)) (p{inv g ⦃ bijective-to-invertible ⦄ (b)})

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    singleton-function : ∀{A : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(A) ⦄ → Function{A = A}(•_)
    _≡_.proof (Function.congruence singleton-function {x} {y} xy) {a} = [↔]-intro (_🝖 symmetry(_≡ₑ_) xy) (_🝖 xy)
