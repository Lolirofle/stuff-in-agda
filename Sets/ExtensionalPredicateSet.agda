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
open import Structure.Container.SetLike as SetLike using (SetLike)
open import Structure.Setoid.WithLvl renaming (_≡_ to _≡ₑ_)
open import Structure.Function.Domain
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
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
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

  filter : (P : T → Stmt{ℓ₁}) ⦃ _ : UnaryRelator(P) ⦄ → PredSet{ℓ₂}(T) → PredSet(T)
  filter P(A) ∋ x = (x ∈ A) ∧ P(x)
  _⨯_.left (UnaryRelator.substitution (preserve-equiv (filter P A)) xy ([∧]-intro xA Px)) = substitute₁(A ∋_) xy xA
  _⨯_.right (UnaryRelator.substitution (preserve-equiv (filter P A)) xy ([∧]-intro xA Px)) = substitute₁(P) xy Px

unapply : ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) ⦃ func-f : Function(f) ⦄ → B → PredSet(A)
unapply f(y) ∋ x = f(x) ≡ₑ y
preserve-equiv (unapply f(y)) = [∘]-unaryRelator ⦃ rel = binary-unaryRelatorᵣ ⦃ rel-P = [≡]-binaryRelator ⦄ ⦄

⊶ : ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) → PredSet(B)
⊶ f ∋ y = ∃(x ↦ f(x) ≡ₑ y)
preserve-equiv (⊶ f) = [∃]-unaryRelator ⦃ rel-P = binary-unaryRelatorₗ ⦃ rel-P = [≡]-binaryRelator ⦄ ⦄

unmap : ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) ⦃ _ : Function(f) ⦄ → PredSet{ℓ}(B) → PredSet(A)
(unmap f(Y)) ∋ x = f(x) ∈ Y
preserve-equiv (unmap f x) = [∘]-unaryRelator

map : ⦃ _ : Equiv{ℓₑ₁}(A) ⦄ ⦃ _ : Equiv{ℓₑ₂}(B) ⦄ → (f : A → B) → PredSet{ℓ}(A) → PredSet(B)
map f(S) ∋ y = ∃(x ↦ (x ∈ S) ∧ (f(x) ≡ₑ y))
preserve-equiv (map f S) = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-Q = binary-unaryRelatorₗ ⦃ rel-P = [≡]-binaryRelator ⦄ ⦄ ⦄

map₂ : ⦃ _ : Equiv{ℓₑ₁}(A₁) ⦄ ⦃ _ : Equiv{ℓₑ₂}(A₂) ⦄ ⦃ _ : Equiv{ℓₑ₃}(B) ⦄ → (_▫_ : A₁ → A₂ → B) → PredSet{ℓ₁}(A₁) → PredSet{ℓ₂}(A₂) → PredSet(B)
map₂(_▫_) S₁ S₂ ∋ y = ∃{Obj = _ ⨯ _}(\{(x₁ , x₂) → (x₁ ∈ S₁) ∧ (x₂ ∈ S₂) ∧ ((x₁ ▫ x₂) ≡ₑ y)})
preserve-equiv (map₂ (_▫_) S₁ S₂) = [∃]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦃ rel-P = [∧]-unaryRelator ⦄ ⦃ rel-Q = binary-unaryRelatorₗ ⦃ rel-P = [≡]-binaryRelator ⦄ ⦄ ⦄

-- Set-set relations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  record _⊆_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) → (x ∈ B)

  record _⊇_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ← (x ∈ B)

  record _≡_ (A : PredSet{ℓ₁}(T)) (B : PredSet{ℓ₂}(T)) : Stmt{ℓₒ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : ∀{x} → (x ∈ A) ↔ (x ∈ B)

  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    Reflexivity.proof [≡]-reflexivity = intro [↔]-reflexivity

  instance
    [≡]-symmetry : Symmetry(_≡_ {ℓ})
    Symmetry.proof [≡]-symmetry (intro xy) = intro([↔]-symmetry xy)

  [≡]-transitivity-raw : ∀{A : PredSet{ℓ₁}(T)}{B : PredSet{ℓ₂}(T)}{C : PredSet{ℓ₃}(T)} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [≡]-transitivity-raw (intro xy) (intro yz) = intro([↔]-transitivity xy yz)

  instance
    [≡]-transitivity : Transitivity(_≡_ {ℓ})
    Transitivity.proof [≡]-transitivity (intro xy) (intro yz) = intro([↔]-transitivity xy yz)

  instance
    [≡]-equivalence : Equivalence(_≡_ {ℓ})
    [≡]-equivalence = intro

  instance
    [≡]-equiv : Equiv(PredSet{ℓ}(T))
    Equiv._≡_ ([≡]-equiv {ℓ}) x y = x ≡ y
    Equiv.equivalence [≡]-equiv = [≡]-equivalence

module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    -- Note: The purpose of this module is to satisfy this property for arbitrary equivalences.
    [∋]-binaryRelator : BinaryRelator(_∋_ {ℓ}{T = T})
    BinaryRelator.substitution [∋]-binaryRelator (intro pₛ) pₑ p = [↔]-to-[→] pₛ(substitute₁(_) pₑ p)

  instance
    [∋]-unaryRelatorₗ : ∀{a : T} → UnaryRelator(A ↦ _∋_ {ℓ} A a)
    [∋]-unaryRelatorₗ = BinaryRelator.left [∋]-binaryRelator

-- TODO: There are level problems here that I am not sure how to solve. The big union of a set of sets are not of the same type as the inner sets. So, for example it would be useful if (⋃ As : PredSet{ℓₒ Lvl.⊔ Lvl.𝐒(ℓ₁)}(T)) and (A : PredSet{ℓ₁}(T)) for (A ∈ As) had the same type/levels when (As : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T))) so that they become comparable. But here, the result of big union is a level greater.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  -- ⋃_ : PredSet{Lvl.𝐒(ℓ₁)}(PredSet{ℓ₁}(T)) → PredSet{ℓₒ Lvl.⊔ Lvl.𝐒(ℓ₁)}(T)
  ⋃ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  (⋃ As) ∋ x = ∃(A ↦ (A ∈ As) ∧ (x ∈ A))
  UnaryRelator.substitution (preserve-equiv (⋃ As)) xy = [∃]-map-proof (Tuple.mapRight (substitute₁(_) xy))

  ⋂ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  (⋂ As) ∋ x = ∀{A} → (A ∈ As) → (x ∈ A)
  UnaryRelator.substitution (preserve-equiv (⋂ As)) xy = substitute₁(_) xy ∘_

-- Indexed set operations.
module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  ⋃ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ Lvl.⊔ ℓ₂}(T)
  (⋃ᵢ Ai) ∋ x = ∃(i ↦ x ∈ Ai(i))
  UnaryRelator.substitution (preserve-equiv (⋃ᵢ Ai)) xy = [∃]-map-proof (\{i} → substitute₁(_) ⦃ preserve-equiv(Ai(i)) ⦄ xy)

  ⋂ᵢ : ∀{I : Type{ℓ₁}} → (I → PredSet{ℓ₂}(T)) → PredSet{ℓ₁ Lvl.⊔ ℓ₂}(T)
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

module _
  {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  {A : Type{ℓ₁}} ⦃ _ : Equiv(A) ⦄
  {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄
  where

  ⋃ᵢ-of-bijection : ∀{f : B → PredSet{ℓ}(T)} ⦃ _ : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋃ᵢ{I = A}(f ∘ g) ≡ ⋃ᵢ{I = B}(f))
  ∃.witness (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = inv g(b)
  ∃.proof (_⨯_.left (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = substitute₂(_∋_) (symmetry(_≡_) (congruence₁(f) inv-inverseᵣ)) (reflexivity(_≡ₑ_)) p
  ∃.witness (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro a ⦃ p ⦄)) = g(a)
  ∃.proof (_⨯_.right (_≡_.proof (⋃ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄))) ([∃]-intro b ⦃ p ⦄)) = p

  ⋂ᵢ-of-bijection : ∀{A : Type{ℓ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓ₂}} ⦃ _ : Equiv(B) ⦄ → ∀{f : B → PredSet{ℓ}(T)} ⦃ _ : Function(f)⦄ → (([∃]-intro g) : A ≍ B) → (⋂ᵢ{I = A}(f ∘ g) ≡ ⋂ᵢ{I = B}(f))
  _⨯_.left (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = p{g(b)}
  _⨯_.right (_≡_.proof (⋂ᵢ-of-bijection {f = f} ([∃]-intro g ⦃ bij-g ⦄)) {x}) p {b} = substitute₂(_∋_) (congruence₁(f) inv-inverseᵣ) (reflexivity(_≡ₑ_)) (p{inv g(b)})

module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    singleton-function : ∀{A : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(A) ⦄ → Function{A = A}(•_)
    _≡_.proof (Function.congruence singleton-function {x} {y} xy) {a} = [↔]-intro (_🝖 symmetry(_≡ₑ_) xy) (_🝖 xy)

module _ {T : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  instance
    PredSet-setLike : SetLike{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike._⊆_ PredSet-setLike = _⊆_
    SetLike._≡_ PredSet-setLike = _≡_
    SetLike.[⊆]-membership PredSet-setLike = [↔]-intro intro _⊆_.proof
    SetLike.[≡]-membership PredSet-setLike = [↔]-intro intro _≡_.proof

  instance
    PredSet-emptySet : SetLike.EmptySet{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.EmptySet.∅          PredSet-emptySet = ∅
    SetLike.EmptySet.membership PredSet-emptySet ()

  instance
    PredSet-universalSet : SetLike.UniversalSet{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.UniversalSet.𝐔          PredSet-universalSet = 𝐔
    SetLike.UniversalSet.membership PredSet-universalSet = record {}

  instance
    PredSet-unionOperator : SetLike.UnionOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.UnionOperator._∪_        PredSet-unionOperator = _∪_
    SetLike.UnionOperator.membership PredSet-unionOperator = [↔]-intro id id

  instance
    PredSet-intersectionOperator : SetLike.IntersectionOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.IntersectionOperator._∩_        PredSet-intersectionOperator = _∩_
    SetLike.IntersectionOperator.membership PredSet-intersectionOperator = [↔]-intro id id

  instance
    PredSet-complementOperator : SetLike.ComplementOperator{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)
    SetLike.ComplementOperator.∁          PredSet-complementOperator = ∁_
    SetLike.ComplementOperator.membership PredSet-complementOperator = [↔]-intro id id

module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓ}(T) ⦄ where -- TODO: Levels in SetLike
  instance
    PredSet-mapFunction : SetLike.MapFunction{C₁ = PredSet{ℓ}(T) ⦃ equiv ⦄}{C₂ = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)(_∈_)
    SetLike.MapFunction.map        PredSet-mapFunction f = map f
    SetLike.MapFunction.membership PredSet-mapFunction   = [↔]-intro id id

  instance
    PredSet-unmapFunction : SetLike.UnmapFunction{C₁ = PredSet{ℓ}(T) ⦃ equiv ⦄}{C₂ = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_)(_∈_)
    SetLike.UnmapFunction.unmap      PredSet-unmapFunction = unmap
    SetLike.UnmapFunction.membership PredSet-unmapFunction = [↔]-intro id id

  instance
    PredSet-unapplyFunction : SetLike.UnapplyFunction{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_) {O = T}
    SetLike.UnapplyFunction.unapply    PredSet-unapplyFunction = unapply
    SetLike.UnapplyFunction.membership PredSet-unapplyFunction = [↔]-intro id id

  instance
    PredSet-filterFunction : SetLike.FilterFunction{C = PredSet{ℓ}(T) ⦃ equiv ⦄} (_∈_) {ℓ}{ℓ}
    SetLike.FilterFunction.filter     PredSet-filterFunction = filter
    SetLike.FilterFunction.membership PredSet-filterFunction = [↔]-intro id id

{- TODO: SetLike is not general enough
module _ {T : Type{ℓ}} ⦃ equiv : Equiv{ℓ}(T) ⦄ where
  instance
    -- PredSet-bigUnionOperator : SetLike.BigUnionOperator{Cₒ = PredSet(PredSet(T) ⦃ {!!} ⦄) ⦃ {!!} ⦄} {Cᵢ = PredSet(T) ⦃ {!!} ⦄} (_∈_)(_∈_)
    SetLike.BigUnionOperator.⋃          PredSet-bigUnionOperator = {!⋃!}
    SetLike.BigUnionOperator.membership PredSet-bigUnionOperator = {!!}
-}
