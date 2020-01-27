-- Sets represented by unary predicates (Like restricted comprehension)
-- Similiar to BoolSet, but instead using the builtin constructive logic with levels.
module Sets.PredicateSet where

import      Lvl
open import Data hiding (Empty)
open import Data.Boolean
open import Data.Boolean.Stmt
open import Functional
open import Function.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
-- open import Relator.Equals.Proofs.Equivalence
open import Sets.Setoid using (Equiv) renaming (_≡_ to _≡ₛ_)
open import Data.Any
open import Structure.Function.Domain
open import Type

module _ where
  -- A set of objects of a certain type.
  -- This is represented by a predicate.
  -- Note: This is only a "set" within a certain type, so everything PredSet(T) is actually a subset of T (if T were a set (the set of all objects with type T)). Or in other words: PredSet(T) is supposed to represent the set {x. x: T}, and then (S ∈ PredSet(T)) essentially means that S when interpreted as a set of objects is a subset of {x. x: T}.
  PredSet : ∀{ℓ ℓₒ} → Type{ℓₒ} → Type{Lvl.𝐒(ℓ) ⊔ ℓₒ}
  PredSet{ℓ}{ℓₒ} (T) = (T → Stmt{ℓ})

  private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓₒ : Lvl.Level
  private variable T A B : Type{ℓₒ}

  -- The statement of whether an element is in a set
  -- TODO: Maybe define this using a equivalence relation instead? (Alternatively a Setoid: x ∈ S = ∃(y ↦ (x ≡_T y) ∧ S(y)))
  _∈_ : T → PredSet{ℓ}(T) → Stmt
  _∈_ = apply -- (x ∈ S) = S(x)

  _∉_ : T → PredSet{ℓ}(T) → Stmt
  _∉_ = (¬_) ∘₂ (_∈_) -- (x ∉ S) = ¬(x ∈ S)

  _∋_ : PredSet{ℓ}(T) → T → Stmt
  _∋_ = swap(_∈_) -- (S ∋ x) = (x ∈ S)

  _∌_ : PredSet{ℓ}(T) → T → Stmt
  _∌_ = (¬_) ∘₂ (_∋_) -- (S ∌ x) = ¬(S ∋ x)

  module BoundedQuantifiers {T : Type{ℓₒ}} where
    ∀ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ ⊔ ℓ₁ ⊔ ℓₒ}
    ∀ₛ(S) P = ∀{elem : T} → (elem ∈ S) → P(elem)

    ∃ₛ : PredSet{ℓ}(T) → (T → Stmt{ℓ₁}) → Stmt{ℓ ⊔ ℓ₁ ⊔ ℓₒ}
    ∃ₛ(S) P = ∃(elem ↦ (elem ∈ S) ∧ P(elem))

  -- An empty set
  ∅ : PredSet{ℓ}(T)
  ∅ = const(Data.Empty)

  -- An universal set
  -- Note: It is only within a certain type, so 𝐔{T} is not actually a subset of everything. It is the greatest subset of subsets of T.
  𝐔 : PredSet{ℓ}(T)
  𝐔 = const(Unit)

  -- A singleton set (a set with only one element)
  •_ : ⦃ Equiv(T) ⦄ → T → PredSet(T)
  •_ = (_≡ₛ_)

  -- An union of two sets
  _∪_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∪_ S₁ S₂ x = (S₁(x) ∨ S₂(x))

  -- An union of a set and a singleton set
  _∪•_ : ∀{ℓ}{T : Type{ℓ}} → PredSet{ℓ₁}(T) → Type{ℓ} → PredSet(T)
  _∪•_ S P x = (S(x) ∨ P)

  -- An intersection of two sets
  _∩_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∩_ S₁ S₂ x = (S₁(x) ∧ S₂(x))

  -- A complement of a set
  ∁_ : PredSet{ℓ}(T) → PredSet(T)
  ∁_ = (¬_) ∘_ -- ∁_ S x = (¬ S(x))

  _∖_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → PredSet(T)
  _∖_ S₁ S₂ = (S₁ ∩ (∁ S₂))

  filter : (T → Bool) → PredSet{ℓ}(T) → PredSet(T)
  filter f S x = (S(x) ∧ IsTrue(f(x)))

  -- A statement of whether a set is a subset of a set
  _⊆_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _⊆_ S₁ S₂ = (∀{x} → (x ∈ S₁) → (x ∈ S₂))

  -- A statement of whether a set is a superset of a set
  _⊇_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _⊇_ S₁ S₂ = (∀{x} → (x ∈ S₁) ← (x ∈ S₂))

  -- A statement of whether a set is equivalent to a set
  _≡_ : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  _≡_ S₁ S₂ = (∀{x} → (x ∈ S₁) ↔ (x ∈ S₂))

  Empty : PredSet{ℓ}(T) → Stmt
  Empty(S) = ∀{x} → ¬(x ∈ S)

  NonEmpty : PredSet{ℓ}(T) → Stmt
  NonEmpty(S) = ∃(_∈ S)

  Disjoint : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  Disjoint S₁ S₂ = ((S₁ ∩ S₂) ⊆ (∅ {Lvl.𝟎}))

  Overlapping : PredSet{ℓ₁}(T) → PredSet{ℓ₂}(T) → Stmt
  Overlapping S₁ S₂ = ∃(S₁ ∩ S₂)

  ⋃_ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  ⋃_ S x = ∃(s ↦ (s ∈ S) ∧ (x ∈ s))

  ⋂_ : PredSet{ℓ₁}(PredSet{ℓ₂}(T)) → PredSet(T)
  ⋂_ S x = ∀{s} → (s ∈ S) → (x ∈ s)

  ℘ : PredSet{ℓ₁}(T) → PredSet(PredSet{ℓ₁}(T))
  ℘ S x = x ⊆ S

  unapply : ⦃ Equiv(B) ⦄ → (f : A → B) → B → PredSet(A)
  unapply f(y) x = f(x) ≡ₛ y

  map : ⦃ Equiv(B) ⦄ → (f : A → B) → PredSet{ℓ}(A) → PredSet(B)
  map f(S) y = Overlapping(S)(unapply f(y))

  unmap : (f : A → B) → PredSet{ℓ}(B) → PredSet(A)
  unmap f(y) x = f(x) ∈ y

  ⊶ : ⦃ Equiv(B) ⦄ → (f : A → B) → PredSet(B)
  ⊶ f y = ∃(unapply f(y))

  module _ where -- TODO: These proofs should be generalized somewhere else?
    open import Structure.Relator.Equivalence
    open import Structure.Relator.Properties

    private variable S : PredSet{ℓ}(T)
    private variable S₁ : PredSet{ℓ₁}(T)
    private variable S₂ : PredSet{ℓ₂}(T)

    instance
      [≡]-reflexivity : Reflexivity(_≡_ {ℓ₁}{ℓ₂}{T})
      Reflexivity.proof [≡]-reflexivity = [↔]-reflexivity

    instance
      [≡]-symmetry : Symmetry(_≡_ {ℓ₁}{ℓ₂}{T})
      Symmetry.proof [≡]-symmetry {x} {y} xy = [↔]-symmetry xy

    instance
      [≡]-transitivity : Transitivity(_≡_ {ℓ₁}{ℓ₂}{T})
      Transitivity.proof [≡]-transitivity {x} {y} {z} xy yz = [↔]-transitivity xy yz

    instance
      [≡]-equivalence : Equivalence(_≡_ {ℓ₁}{ℓ₂}{T})
      [≡]-equivalence = intro

    {- TODO: Cannot be an instance of Equiv because of level issues
    instance
      [≡]-equiv : Equiv(PredSet{ℓ}(T))
      Equiv._≡_ [≡]-equiv = {!_≡_!}
      Equiv.[≡]-equivalence [≡]-equiv = {![≡]-equivalence!}
    -}

    [≡]-to-[⊆] : (S₁ ≡ S₂) → (S₁ ⊆ S₂)
    [≡]-to-[⊆] S₁S₂ {x} = [↔]-to-[→] (S₁S₂{x})

    [≡]-to-[⊇] : (S₁ ≡ S₂) → (S₁ ⊇ S₂)
    [≡]-to-[⊇] S₁S₂ {x} = [↔]-to-[←] (S₁S₂{x})

    [⊆]-of-[∪]ₗ : (S₁ ⊆ (S₁ ∪ S₂))
    [⊆]-of-[∪]ₗ = [∨]-introₗ

    [⊆]-of-[∪]ᵣ : (S₂ ⊆ (S₁ ∪ S₂))
    [⊆]-of-[∪]ᵣ = [∨]-introᵣ

    [∪]-of-subset : (S₁ ⊆ S₂) → ((S₁ ∪ S₂) ≡ S₂)
    [∪]-of-subset S₁S₂ = [↔]-intro [∨]-introᵣ ([∨]-elim S₁S₂ id)

    [⊆]-min : (∅ {ℓ} ⊆ S)
    [⊆]-min = empty
    
    [⊆]-max : (S ⊆ 𝐔 {ℓ})
    [⊆]-max = const <>

    [∅]-containment : ∀{x : T} → ¬(x ∈ ∅ {ℓ})
    [∅]-containment = empty

    [𝐔]-containment : ∀{x : T} → (x ∈ 𝐔 {ℓ})
    [𝐔]-containment = <>

    map-containmentₗ : ⦃ equiv-B : Equiv(B) ⦄ → ∀{x : A}{f : A → B} → (f(x) ∈ map ⦃ equiv-B ⦄ f(S)) ← (x ∈ S)
    map-containmentₗ {x = x} = (xS ↦ [∃]-intro x ⦃ [↔]-intro xS (reflexivity(_≡ₛ_)) ⦄)

    -- map-containmentᵣ : ⦃ _ : Relation(S) ⦄ → ∀{f : A → B} → ⦃ _ : Injective(f) ⦄ → ∀{x : A} → (f(x) ∈ map f(S)) → (x ∈ S)
    -- map-containmentᵣ {x = x} = ([∃]-intro a ⦃ [∧]-intro p q ⦄) ↦ {!!}

    [⋂]-of-[∅] : ((⋂_ {ℓ₁}{ℓ₂} ∅) ≡ 𝐔 {ℓ₃}{ℓ₄}{T})
    [⋂]-of-[∅] = [↔]-intro (const empty) (const <>)

    [⋂]-of-[𝐔] : ((⋂_ {ℓ₁}{ℓ₂} 𝐔) ≡ ∅ {ℓ₂}{ℓ₃}{T})
    [⋂]-of-[𝐔] {ℓ₁}{ℓ₂}{ℓ₃}{T} = [↔]-intro empty (inters ↦ inters([𝐔]-containment{x = ∅ {ℓ₂}{ℓ₃}{T}}))

    [⋃]-of-[∅] : ((⋃_ {ℓ₁}{ℓ₂} ∅) ≡ ∅ {ℓ₁}{ℓ₃}{T})
    [⋃]-of-[∅] = [↔]-intro empty (([∃]-intro s ⦃ [∧]-intro p _ ⦄) ↦ p)

    [⋃]-of-[𝐔] : ((⋃_ {ℓ₁}{ℓ₂} 𝐔) ≡ 𝐔 {ℓ₃}{ℓ₄}{T})
    [⋃]-of-[𝐔] {ℓ₁}{ℓ₂}{ℓ₃}{T} = [↔]-intro (const ([∃]-intro 𝐔 ⦃ [↔]-intro <> <> ⦄)) (const <>)

    -- Disjoint-irreflexivity : ⦃ _ : NonEmpty(_) ⦄ → Irreflexivity(Disjoint{ℓ₁}{ℓ₂}{T})
    -- Irreflexivity.proof Disjoint-irreflexivity p = {!!}

    SetType : PredSet{ℓ}(T) → Stmt
    SetType(s) = ∃(_∈ s)

    {-
    choice : ∀{S : PredSet{ℓ₁}(PredSet{ℓ₂}(T))} → ∃{Obj = SetType(S) → SetType(⋃ S)}(f ↦ ∀{([∃]-intro x) : SetType(S)} → ([∃]-witness(f([∃]-intro x)) ∈ x))
    ∃.witness (∃.witness (choice {S = S}) ([∃]-intro f ⦃ proof ⦄)) = {!!}
    ∃.proof   (∃.witness (choice {S = S}) ([∃]-intro f ⦃ proof ⦄)) = {!!}
    ∃.proof              (choice {S = S}) {[∃]-intro f ⦃ proof ⦄}  = {!!}
    -}
  
