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
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Sets.Setoid using (Equiv ; Function ; UnaryRelator ; BinaryRelator ; substitute₁ ; substitute₂ ; [≡]-with ; [≡]-with2ₗ ; [≡]-with2ᵣ) renaming (_≡_ to _≡ₑ_)
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Size

private variable ℓ ℓₒ ℓ₁ ℓ₂ : Lvl.Level

-- A set of objects of a certain type where equality is based on setoids.
-- This is defined by the containment predicate (_∋_) and a proof that it respects the setoid structure.
-- (A ∋ a) is read "The set A contains the element a".
-- Note: This is only a "set" within a certain type, so the collection PredSet(T) is actually a subcollection of T.
record PredSet {ℓ ℓₒ} (T : Type{ℓₒ}) ⦃ equiv : Equiv(T) ⦄ : Type{Lvl.𝐒(ℓ) ⊔ ℓₒ} where
  constructor intro
  field
    _∋_ : T → Stmt{ℓ}
    ⦃ preserve-equiv ⦄ : UnaryRelator(_∋_)
open PredSet using (_∋_) public
open PredSet using (preserve-equiv)

-- Element-set relations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  -- The inclusion relation.
  -- (a ∈ A) is read "The element a is included in the set A".
  _∈_ : T → PredSet{ℓ}(T) → Stmt
  _∈_ = swap(_∋_)

  _∉_ : T → PredSet{ℓ}(T) → Stmt
  _∉_ = (¬_) ∘₂ (_∈_)

  _∌_ : PredSet{ℓ}(T) → T → Stmt
  _∌_ = (¬_) ∘₂ (_∋_)

-- Set-bounded quantifiers.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  ∀ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ ⊔ ℓ₁ ⊔ ℓₒ}
  ∀ₛ(S) P = ∀{elem : T} → (elem ∈ S) → P(elem)

  ∃ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ ⊔ ℓ₁ ⊔ ℓₒ}
  ∃ₛ(S) P = ∃(elem ↦ (elem ∈ S) ∧ P(elem))

-- Sets and set operations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  -- An empty set.
  -- Contains nothing.
  ∅ : PredSet{ℓ}(T)
  ∅ ∋ x = Empty
  UnaryRelator.substitution (preserve-equiv ∅) = const id

  -- An universal set.
  -- Contains everything.
  -- Note: Everything as in every object of type  T.
  𝐔 : PredSet{ℓ}(T)
  𝐔 ∋ x = Unit
  UnaryRelator.substitution (preserve-equiv 𝐔) = const id

  -- A singleton set (a set containing only one element).
  •_ : T → PredSet(T)
  (• a) ∋ x = x ≡ₑ a
  UnaryRelator.substitution (preserve-equiv (• a)) xy xa = symmetry(_≡ₑ_) xy 🝖 xa

  -- An union of two sets.
  -- Contains the elements that any of the both sets contain.
  _∪_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  (A ∪ B) ∋ x = (A ∋ x) ∨ (B ∋ x)
  UnaryRelator.substitution (preserve-equiv (A ∪ B)) xy = Either.map2 (substitute₁(A ∋_) xy) (substitute₁(B ∋_) xy)

  -- An intersection of two sets.
  -- Contains the elements that both of the both sets contain.
  _∩_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  (A ∩ B) ∋ x = (A ∋ x) ∧ (B ∋ x)
  UnaryRelator.substitution (preserve-equiv (A ∩ B)) xy = Tuple.map (substitute₁(A ∋_) xy) (substitute₁(B ∋_) xy)

  -- A complement of a set.
  -- Contains the elements that the set does not contain.
  ∁_ : PredSet{ℓ}(T) → PredSet(T)
  (∁ A) ∋ x = A ∌ x
  UnaryRelator.substitution (preserve-equiv (∁ A)) xy = contrapositiveᵣ (substitute₁(A ∋_) (symmetry(_≡ₑ_) xy))

  -- A relative complement of a set.
  -- Contains the elements that the left set contains without the elements included in the right set..
  _∖_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  A ∖ B = (A ∩ (∁ B))

-- Set-set relations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  record _⊆_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ ⊔ ℓ₁ ⊔ Lvl.𝐒(ℓ₂)} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) → (x ∈ B)

  record _⊇_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ ⊔ ℓ₁ ⊔ Lvl.𝐒(ℓ₂)} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ← (x ∈ B)

  record _≡_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ ⊔ ℓ₁ ⊔ Lvl.𝐒(ℓ₂)} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ↔ (x ∈ B)

  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    Reflexivity.proof [≡]-reflexivity = intro [↔]-reflexivity

  instance
    [≡]-symmetry : Symmetry(_≡_ {ℓ})
    Symmetry.proof [≡]-symmetry (intro xy) = intro([↔]-symmetry xy)

  instance
    [≡]-transitivity : Transitivity(_≡_ {ℓ})
    Transitivity.proof [≡]-transitivity (intro xy) (intro yz) = intro([↔]-transitivity xy yz)

  instance
    [≡]-equivalence : Equivalence(_≡_ {ℓ})
    [≡]-equivalence = intro

  instance
    [≡]-equiv : Equiv(PredSet{ℓ}(T))
    Equiv._≡_ ([≡]-equiv {ℓ}) x y = x ≡ y
    Equiv.[≡]-equivalence [≡]-equiv = [≡]-equivalence

module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  instance
    -- Note: The purpose of this module is to satisfy this property for arbitrary equivalences.
    [∋]-binaryRelator : BinaryRelator(_∋_ {ℓ}{T = T})
    BinaryRelator.substitution [∋]-binaryRelator (intro pₛ) pₑ p = [↔]-to-[→] pₛ(substitute₁(_) pₑ p)

-- TODO: There are level problems here that I am not sure how to solve. The big union of a set of sets are not of the same type as the inner sets. So, for example it would be useful if (⋃ As : PredSet{ℓₒ ⊔ Lvl.𝐒(ℓ₁)}(T)) and (A : PredSet{ℓ₁}(T)) for (A ∈ As) had the same type/levels when (As : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T))) so that they become comparable. But here, the result of big union is a level greater.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  -- ⋃_ : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T)) → PredSet{ℓₒ ⊔ Lvl.𝐒(ℓ₁)}(T)
  ⋃ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet{ℓₒ ⊔ ℓ₁ ⊔ Lvl.𝐒(ℓ₂)}(T)
  (⋃ As) ∋ x = ∃(A ↦ (A ∈ As) ∧ (x ∈ A))
  UnaryRelator.substitution (preserve-equiv (⋃ As)) xy = [∃]-map-proof (Tuple.mapRight (substitute₁(_) xy))

  ⋂ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet{ℓₒ ⊔ ℓ₁ ⊔ Lvl.𝐒(ℓ₂)}(T)
  (⋂ As) ∋ x = ∀{A} → (A ∈ As) → (x ∈ A)
  UnaryRelator.substitution (preserve-equiv (⋂ As)) xy = substitute₁(_) xy ∘_

-- Indexed set operations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv(T) ⦄ where
  ⋃ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ ⊔ ℓ₂}(T)
  (⋃ᵢ Ai) ∋ x = ∃(i ↦ x ∈ Ai(i))
  UnaryRelator.substitution (preserve-equiv (⋃ᵢ Ai)) xy = [∃]-map-proof (\{i} → substitute₁(_) ⦃ preserve-equiv(Ai(i)) ⦄ xy)

  ⋂ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ ⊔ ℓ₂}(T)
  (⋂ᵢ Ai) ∋ x = ∀ₗ(i ↦ x ∈ Ai(i))
  UnaryRelator.substitution (preserve-equiv (⋂ᵢ Ai)) xy p {i} = substitute₁(_) ⦃ preserve-equiv(Ai(i)) ⦄ xy p

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

  ⋃ᵢ-of-bijection : ∀{A : Type{ℓ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ → ∀{f : B → PredSet{ℓ}(T)} ⦃ _ : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋃ᵢ{I = A}(f ∘ g) ≡ ⋃ᵢ{I = B}(f))
  ∃.witness (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = inv g(b)
  ∃.proof (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = substitute₂(_∋_) (symmetry(_≡_) ([≡]-with(f) inv-inverseᵣ)) (reflexivity(_≡ₑ_)) p
  ∃.witness (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro a ⦃ p ⦄)) = g(a)
  ∃.proof (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = p

  ⋂ᵢ-of-bijection : ∀{A : Type{ℓ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ → ∀{f : B → PredSet{ℓ}(T)} ⦃ _ : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋂ᵢ{I = A}(f ∘ g) ≡ ⋂ᵢ{I = B}(f))
  _⨯_.left (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = p{g(b)}
  _⨯_.right (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = substitute₂(_∋_) ([≡]-with(f) inv-inverseᵣ) (reflexivity(_≡ₑ_)) (p{inv g(b)})
