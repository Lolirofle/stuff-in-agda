import      Lvl
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Logic.Propositional.Theorems{Lvl.𝟎}
open import Type{Lvl.𝟎}

-- Based on https://plato.stanford.edu/entries/set-theory-constructive/axioms-CZF-IZF.html (2017-10-13)
module Sets.IZF (S : Set(Lvl.𝟎)) (_∈_ : S → S → Stmt) where

module Relations where
  _∉_ : S → S → Stmt
  _∉_ x a = ¬(x ∈ a)

  _⊆_ : S → S → Stmt
  _⊆_ a b = (∀{x} → (x ∈ a) → (x ∈ b))

  _⊇_ : S → S → Stmt
  _⊇_ a b = (∀{x} → (x ∈ a) ← (x ∈ b))

  _≡_ : S → S → Stmt
  _≡_ a b = (∀{x} → (x ∈ a) ↔ (x ∈ b))

  -- The statement that the set s is empty
  Empty : S → Stmt
  Empty(s) = (∀{x} → (x ∉ s))

  -- The statement that the set s is inhabited/non-empty
  NonEmpty : S → Stmt
  NonEmpty(s) = ∃(x ↦ (x ∈ s))

  -- The statement that the set s is a singleton set containing only the single element x₁
  Singleton : S → S → Stmt
  Singleton(s) (x₁) = (∀{x} → (x ∈ s) ↔ (x ≡ x₁))

  -- The statement that the set s is a pair set containing only the two elements x₁, x₂
  Pair : S → S → S → Stmt
  Pair(s) (x₁)(x₂) = (∀{x} → (x ∈ s) ↔ (x ≡ x₁)∨(x ≡ x₂))

  -- The statement that the set sᵤ is the union of the sets s₁, s₂
  Union : S → S → S → Stmt
  Union(sᵤ) (s₁)(s₂) = (∀{x} → (x ∈ sᵤ) ↔ (x ∈ s₁)∨(x ∈ s₂))

  -- The statement that the set sᵤ is the intersection of the sets s₁, s₂
  Intersection : S → S → S → Stmt
  Intersection(sᵢ) (s₁)(s₂) = (∀{x} → (x ∈ sᵢ) ↔ (x ∈ s₁)∧(x ∈ s₂))

  -- The statement that the set sₚ is the power set of s
  Power : S → S → Stmt
  Power(sₚ) (s) = (∀{x} → (x ∈ sₚ) ↔ (x ⊆ s))

  -- The statement that the set sᵤ is the union of all sets in ss
  UnionAll : S → S → Stmt
  UnionAll(sᵤ) (ss) = (∀{x s} → (x ∈ sᵤ) ↔ (x ∈ s)∧(s ∈ ss))

  -- The statement that the set sᵤ is the intersection of all sets in ss
  IntersectionAll : S → S → Stmt
  IntersectionAll(sᵢ) (ss) = (∀{x} → (x ∈ sᵢ) ↔ (∀{s} → (s ∈ ss) → (x ∈ s)))

  -- The statement that the set sₛ is the subset of s where every element satisfies φ
  FilteredSubset : S → S → (S → Stmt) → Stmt
  FilteredSubset(sₛ) (s)(φ) = (∀{x} → (x ∈ sₛ) ↔ ((x ∈ s) ∧ φ(x)))

module RelationsTheorems where
  open Relations

  [≡]-reflexivity : ∀{s} → (s ≡ s)
  [≡]-reflexivity = [↔]-reflexivity

  [≡]-transitivity : ∀{s₁ s₂ s₃} → (s₁ ≡ s₂) → (s₂ ≡ s₃) → (s₁ ≡ s₃)
  [≡]-transitivity(s12)(s23){x} = [↔]-transitivity(s12{x})(s23{x})

  [≡]-symmetry : ∀{s₁ s₂} → (s₁ ≡ s₂) → (s₂ ≡ s₁)
  [≡]-symmetry(s12){x} = [↔]-symmetry(s12{x})

  -- TODO: Are these even provable with my def. of set equality?
  -- [≡]-substitute : ∀{φ : S → Stmt}{s₁ s₂} → (s₁ ≡ s₂) → ∀{x} → φ(s₁) ↔ φ(s₂)
  -- [≡]-substituteₗ : ∀{φ : Stmt → Stmt}{s₁ s₂} → (s₁ ≡ s₂) → ∀{x} → φ(s₁ ∈ x) ↔ φ(s₂ ∈ x)

  [⊆]-reflexivity : ∀{s} → (s ⊆ s)
  [⊆]-reflexivity = [→]-reflexivity

  [⊆]-transitivity : ∀{s₁ s₂ s₃} → (s₁ ⊆ s₂) → (s₂ ⊆ s₃) → (s₁ ⊆ s₃)
  [⊆]-transitivity(s12)(s23){x} = [→]-transitivity(s12{x})(s23{x})

  [⊆]-antisymmetry : ∀{s₁ s₂} → (s₁ ⊇ s₂) → (s₁ ⊆ s₂) → (s₁ ≡ s₂)
  [⊆]-antisymmetry(s21)(s12){x} = [↔]-intro (s21{x}) (s12{x})

module Axioms1 where
  open Relations

  -- Axiom of the empty set
  -- A set which is empty exists.
  record EmptySetExistence : Set(Lvl.𝟎) where
    field empty : ∃(s ↦ Empty(s))
  open EmptySetExistence ⦃ ... ⦄ public

  -- Axiom of pairing
  -- A set with two elements exists.
  record PairExistence : Set(Lvl.𝟎) where
    field pair : ∀{x₁ x₂} → ∃(s ↦ Pair(s)(x₁)(x₂))
  open PairExistence ⦃ ... ⦄ public

  -- Axiom of union
  -- A set which contains all the elements of a group of sets exists.
  record UnionExistence : Set(Lvl.𝟎) where
    field union : ∀{ss} → ∃(sᵤ ↦ UnionAll(sᵤ)(ss))
  open UnionExistence ⦃ ... ⦄ public

  -- Axiom of the power set
  -- A set which contains all the subsets of a set exists.
  record PowerSetExistence : Set(Lvl.𝟎) where
    field power : ∀{s} → ∃(sₚ ↦ Power(sₚ)(s))
  open PowerSetExistence ⦃ ... ⦄ public

  -- Axiom schema of restricted comprehension | Axiom schema of specification | Axiom schema of separation
  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  record RestrictedComprehensionExistence : Set(Lvl.𝐒(Lvl.𝟎)) where
    field comprehension : ∀{s}{φ : S → Stmt} → ∃(sₛ ↦ FilteredSubset(sₛ)(s)(φ))
  open RestrictedComprehensionExistence ⦃ ... ⦄ public

  -- Axiom schema of collection
  -- A set which collects all RHS in a binary relation (and possibly more elements) exists.
  -- The image of a function has a superset?
  -- Detailed explanation:
  --   Given a set a and a formula φ:
  --   If ∀(x∊a)∃y. φ(x)(y)
  --     The binary relation φ describes a total multivalued function from the set a to b:
  --       φ: a→b
  --     Note: φ is not neccessarily a set.
  --   Then ∃b∀(x∊a)∃(y∊b). φ(x)(y)
  --     There exists a set b such that every argument of the function has one of its function values in it.
  record CollectionAxiom : Set(Lvl.𝐒(Lvl.𝟎)) where
    field collection : ∀{φ : S → S → Stmt} → ∀{a} → (∀{x} → (x ∈ a) → ∃(y ↦ φ(x)(y))) → ∃(b ↦ ∀{x} → (x ∈ a) → ∃(y ↦ ((y ∈ b) ∧ φ(x)(y))))
  open CollectionAxiom ⦃ ... ⦄ public

  -- Induction proof on sets.
  -- This can be used to prove stuff about all sets.
  -- This can be interpreted as:
  --   A proof of a predicate satisfying every element of an arbitrary set is a proof of this predicate satisfying every set.
  record InductionProof : Set(Lvl.𝐒(Lvl.𝟎)) where
    field induction : ∀{φ : S → Stmt} → (∀{s} → (∀{x} → (x ∈ s) → φ(x)) → φ(s)) → (∀{s} → φ(s))
  open InductionProof ⦃ ... ⦄ public

module Theorems1 where
  open Axioms1
  open Relations

  module _ ⦃ _ : PairExistence ⦄ where
      -- A set with only one element exists.
    single : ∀{x₁} → ∃(s ↦ (∀{x} → (x ∈ s) ↔ (x ≡ x₁)))
    single{x} with pair{x}{x}
    ...          | [∃]-intro (z) (f) = ([∃]-intro (z) (\{w} → [↔]-transitivity (f{w}) [∨]-redundancy))

  module _ ⦃ _ : EmptySetExistence ⦄ where
    [∅]-uniqueness : ∀{x y} → Empty(x) → Empty(y) → (x ≡ y)
    [∅]-uniqueness (empty-x)(empty-y) =
      ([↔]-intro
        ([⊥]-elim ∘ empty-y)
        ([⊥]-elim ∘ empty-x)
      )

  {-
    Singleton-elem-uniqueness : ∀{x y₁ y₂} → (y₁ ∈ Singleton(x)) → (y₂ ∈ Singleton(x)) → (y₁ ≡ y₂)
    Singleton-elem-uniqueness (y₁-proof)(y₂-proof) =
      ([↔]-intro
        (y₁-proof)
        (y₂-proof)
      )
  -}

module Operations where
  open Axioms1
  open Relations
  open Theorems1

  module _ ⦃ _ : EmptySetExistence ⦄ where
    -- Definition of the empty set: ∅={}.
    -- This can be used to construct a set with no elements.
    ∅ : S
    ∅ = [∃]-extract(empty)

  module _ ⦃ _ : PairExistence ⦄ where
    -- Definition of a singleton set: {x} for some element x.
    -- This can be used to construct a set with a single element.
    • : S → S
    •(x) = [∃]-extract(single{x})

    -- Definition of a pair set: {x,y} for some elements x and y.
    -- This can be used to construct a set with a countable number of elements: x⟒y⟒z.
    _⟒_ : S → S → S
    _⟒_ (x)(y) = [∃]-extract(pair{x}{y})

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    -- Definition of the union of two sets: s₁∪s₂ for two sets s₁ and s₂
    -- This can be used to construct a set that contains all elements from either of the two sets.
    _∪_ : S → S → S
    _∪_ s₁ s₂ = [∃]-extract(union{s₁ ⟒ s₂})

  module _ ⦃ _ : UnionExistence ⦄ where
    -- Definition of the union of a set of sets: ⋃(ss) for a set of sets ss
    -- This can be used to construct a set that contains all elements from the sets.
    reduce-[∪] : S → S
    reduce-[∪] ss = [∃]-extract(union{ss})

  module _ ⦃ _ : PowerSetExistence ⦄ where
    -- Definition of the power set of a set: ℘(s) for some set s
    -- This can be used to construct a set that contains all subsets of a set.
    ℘ : S → S
    ℘(s) = [∃]-extract(power{s})

  module _ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    -- Definition of the usual "set builder notation": {x∊s. φ(x)} for some set s
    -- This can be used to construct a set that is the subset which satisfies a certain predicate for every element.
    filter : S → (S → Stmt) → S
    filter(s)(φ) = [∃]-extract(comprehension{s}{φ})

    -- Definition of the intersection of two sets: s₁∩s₂ for two sets s₁ and s₂
    -- This can be used to construct a set that contains all elements that only are in both sets.
    _∩_ : S → S → S
    _∩_ (s₁)(s₂) = filter(s₁)(x ↦ (x ∈ s₂))

    -- Definition of the intersection of a set of sets: ⋃(ss) for a set of sets ss
    -- This can be used to construct a set that contains all elements that only are in all of the sets.
    -- reduce-[∪] : S → S
    -- reduce-[∪] ss = filter(s₁)(x ↦ (x ∈ s₂))

    -- Definition of the subtraction of two sets: s₁∖s₂ for two sets s₁ and s₂
    -- This can be used to construct a set that contains all elements from s₁ which is not in s₂.
    _∖_ : S → S → S
    _∖_ (s₁)(s₂) = filter(s₁)(_∉ s₂)

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    -- Definition of the intersection of a set of sets: ⋂(ss) for a set of sets ss
    -- This can be used to construct a set that only contains the elements which all the sets have in common.
    reduce-[∩] : S → S
    reduce-[∩] ss = filter(reduce-[∪] (ss))(x ↦ ∀{s} → (s ∈ ss) → (x ∈ s))

module OperationsTheorems where
  open Axioms1
  open Operations
  open Relations
  open Theorems1
  open Relations
  open RelationsTheorems

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Containment

  module _ ⦃ _ : EmptySetExistence ⦄ where
    [∅]-containment : Empty(∅)
    [∅]-containment = [∃]-property(empty)

  module _ ⦃ _ : PairExistence ⦄ where
    [•]-containment : ∀{x₁} → (x₁ ∈ •(x₁))
    [•]-containment{x₁} = [↔]-elimₗ([∃]-property(single{x₁})) ([≡]-reflexivity)

    [⟒]-containment : ∀{x₁ x₂}{x} → (x ∈ (x₁ ⟒ x₂)) ↔ (x ≡ x₁)∨(x ≡ x₂)
    [⟒]-containment{x₁}{x₂} = [∃]-property(pair{x₁}{x₂})

    [⟒]-containmentₗ : ∀{x₁ x₂} → (x₁ ∈ (x₁ ⟒ x₂))
    [⟒]-containmentₗ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introₗ([≡]-reflexivity))

    [⟒]-containmentᵣ : ∀{x₁ x₂} → (x₂ ∈ (x₁ ⟒ x₂))
    [⟒]-containmentᵣ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introᵣ([≡]-reflexivity))

  module _ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    filter-containment : ∀{s}{φ}{x} → (x ∈ filter(s)(φ)) ↔ ((x ∈ s) ∧ φ(x))
    filter-containment{s} = [∃]-property(comprehension)

    [∩]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∩ s₂)) ↔ (x ∈ s₁)∧(x ∈ s₂)
    [∩]-containment = filter-containment

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    [∪]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ↔ (x ∈ s₁)∨(x ∈ s₂)
    [∪]-containment = [↔]-intro [∪]-containmentₗ [∪]-containmentᵣ where
      postulate [∪]-containmentₗ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ← (x ∈ s₁)∨(x ∈ s₂)
      postulate [∪]-containmentᵣ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) → (x ∈ s₁)∨(x ∈ s₂)

  module _ ⦃ _ : PowerSetExistence ⦄ where
    [℘]-containment : ∀{s sₛ} → (sₛ ⊆ s) ↔ (sₛ ∈ ℘(s))
    [℘]-containment{s} = [↔]-symmetry([∃]-property(power{s}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Other

  module _ ⦃ _ : EmptySetExistence ⦄ where
    [∅]-in-subset : ∀{s} → (∅ ⊆ s)
    [∅]-in-subset = [⊥]-elim ∘ [∅]-containment

  module _ ⦃ _ : EmptySetExistence ⦄ ⦃ _ : PowerSetExistence ⦄ where
    [℘][∅]-containment : ∀{s} → (∅ ∈ ℘(s))
    [℘][∅]-containment = [↔]-elimᵣ([℘]-containment)([∅]-in-subset)

  module _ ⦃ _ : PowerSetExistence ⦄ where
    [℘]-set-containment : ∀{s} → (s ∈ ℘(s))
    [℘]-set-containment = [↔]-elimᵣ([℘]-containment)([⊆]-reflexivity)

  module _ ⦃ _ : InductionProof ⦄ where
    self-noncontainment : ∀{s} → (s ∉ s) -- ¬ ∃(s ↦ s ∈ s)
    self-noncontainment = induction{x ↦ x ∉ x} (proof) where
      proof : ∀{s} → (∀{x} → (x ∈ s) → (x ∉ x)) → (s ∉ s)
      proof{s} (f)(s∈s) = f{s}(s∈s)(s∈s)
      -- ∀{s} → (∀{x} → (x ∈ s) → (x ∉ x)) → (s ∉ s)
      -- ∀{s} → (∀{x} → (x ∈ s) → (x ∈ x) → ⊥) → (s ∈ s) → ⊥

    [𝐔]-nonexistence : ¬ ∃(𝐔 ↦ ∀{x} → (x ∈ 𝐔))
    [𝐔]-nonexistence ([∃]-intro 𝐔 proof) = self-noncontainment {𝐔} (proof{𝐔})

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Subset

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    [∪]-subsetₗ : ∀{s₁ s₂} → (s₁ ⊆ (s₁ ∪ s₂))
    [∪]-subsetₗ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introₗ

    [∪]-subsetᵣ : ∀{s₁ s₂} → (s₂ ⊆ (s₁ ∪ s₂))
    [∪]-subsetᵣ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introᵣ

    postulate [∪]-subset-eq : ∀{s₁ s₂ s₃} → ((s₁ ∪ s₂) ⊆ s₃) ↔ ((s₁ ⊆ s₃)∧(s₂ ⊆ s₃))

  module _ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    [∩]-subsetₗ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₁)
    [∩]-subsetₗ = [∧]-elimₗ ∘ ([↔]-elimᵣ([∩]-containment))

    [∩]-subsetᵣ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₂)
    [∩]-subsetᵣ = [∧]-elimᵣ ∘ ([↔]-elimᵣ([∩]-containment))

    filter-subset : ∀{s}{φ} → (filter(s)(φ) ⊆ s)
    filter-subset{s}{φ} {x}(x∈s) = [∧]-elimₗ([↔]-elimᵣ([∃]-property(comprehension{s}{φ}))(x∈s))

  module _ ⦃ _ : PowerSetExistence ⦄ where
    [℘]-subset : ∀{s₁ s₂} → (s₁ ⊆ s₂) ↔ (℘(s₁) ⊆ ℘(s₂))
    [℘]-subset = [↔]-intro l r where
      l : ∀{s₁ s₂} → (s₁ ⊆ s₂) ← (℘(s₁) ⊆ ℘(s₂))
      l {s₁}{s₂} (p1p2) = ([↔]-elimₗ [℘]-containment) (p1p2{s₁} ([℘]-set-containment))

      r : ∀{s₁ s₂} → (s₁ ⊆ s₂) → (℘(s₁) ⊆ ℘(s₂))
      r {s₁}{s₂} (s12) {a} (aps1) = ([↔]-elimᵣ [℘]-containment) ([⊆]-transitivity (([↔]-elimₗ [℘]-containment) aps1) (s12))

  -- TODO: Does this hold: Empty(s) ∨ NonEmpty(s) ? Probably not

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Commutativity

  -- [⟒]-commutativity : ∀{s₁ s₂} → (s₁ ⟒ s₂) ≡ (s₂ ⟒ s₁)
  -- [⟒]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
  --   f : ∀{s₁ s₂} → (x ∈ (s₁ ⟒ s₂)) → (x ∈ (s₂ ⟒ s₁))
  --   f{s₁}{s₂} = ([↔]-elimₗ([⟒]-containment{s₂}{s₁}{x})) ∘ ([∨]-symmetry) ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    [∪]-commutativity : ∀{s₁ s₂} → (s₁ ∪ s₂) ≡ (s₂ ∪ s₁)
    [∪]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
      f : ∀{s₁ s₂} → (x ∈ (s₁ ∪ s₂)) → (x ∈ (s₂ ∪ s₁))
      f{s₁}{s₂} =
        ([↔]-elimₗ([∪]-containment{s₂}{s₁}{x}))
        ∘ ([∨]-symmetry)
        ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  module _ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    [∩]-commutativity : ∀{s₁ s₂} → (s₁ ∩ s₂) ≡ (s₂ ∩ s₁)
    [∩]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
      f : ∀{s₁ s₂} → (x ∈ (s₁ ∩ s₂)) → (x ∈ (s₂ ∩ s₁))
      f{s₁}{s₂} =
        ([↔]-elimₗ([∩]-containment{s₂}{s₁}{x}))
        ∘ ([∧]-symmetry)
        ∘ ([↔]-elimᵣ([∩]-containment{s₁}{s₂}{x}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Associativity

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    [∪]-associativity : ∀{s₁ s₂ s₃} → ((s₁ ∪ s₂) ∪ s₃) ≡ (s₁ ∪ (s₂ ∪ s₃))
    [∪]-associativity{s₁}{s₂}{s₃} {x} = [↔]-intro l r where
      l : (x ∈ ((s₁ ∪ s₂) ∪ s₃)) ← (x ∈ (s₁ ∪ (s₂ ∪ s₃)))
      l = ([↔]-elimₗ([∪]-containment{s₁ ∪ s₂}{s₃}{x}))
        ∘ ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimₗ([∪]-containment{s₁}{s₂}{x}))) ([∨]-introᵣ))
        ∘ ([↔]-elimₗ [∨]-associativity)
        ∘ ([∨]-elim ([∨]-introₗ) ([∨]-introᵣ ∘ ([↔]-elimᵣ([∪]-containment{s₂}{s₃}{x}))))
        ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂ ∪ s₃}{x}))

      r : (x ∈ ((s₁ ∪ s₂) ∪ s₃)) → (x ∈ (s₁ ∪ (s₂ ∪ s₃)))
      r = ([↔]-elimₗ([∪]-containment{s₁}{s₂ ∪ s₃}{x}))
        ∘ ([∨]-elim ([∨]-introₗ) ([∨]-introᵣ ∘ ([↔]-elimₗ([∪]-containment{s₂}{s₃}{x}))))
        ∘ ([↔]-elimᵣ [∨]-associativity)
        ∘ ([∨]-elim ([∨]-introₗ ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))) ([∨]-introᵣ))
        ∘ ([↔]-elimᵣ([∪]-containment{s₁ ∪ s₂}{s₃}{x}))

  module _ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    [∩]-associativity : ∀{s₁ s₂ s₃} → ((s₁ ∩ s₂) ∩ s₃) ≡ (s₁ ∩ (s₂ ∩ s₃))
    [∩]-associativity{s₁}{s₂}{s₃} {x} = [↔]-intro l r where
      l : (x ∈ ((s₁ ∩ s₂) ∩ s₃)) ← (x ∈ (s₁ ∩ (s₂ ∩ s₃)))
      l = (([↔]-elimₗ([∩]-containment{s₁ ∩ s₂}{s₃}{x}))                                                   :of: ((x ∈ ((s₁ ∩ s₂) ∩ s₃)) ← (x ∈ (s₁ ∩ s₂))∧(x ∈ s₃)))
        ∘ ((prop ↦ ([∧]-intro ([↔]-elimₗ([∩]-containment{s₁}{s₂}{x}) ([∧]-elimₗ prop)) ([∧]-elimᵣ prop))) :of: ((x ∈ (s₁ ∩ s₂))∧(x ∈ s₃) ← ((x ∈ s₁)∧(x ∈ s₂))∧(x ∈ s₃)))
        ∘ ([↔]-elimₗ [∧]-associativity)
        ∘ ((prop ↦ ([∧]-intro ([∧]-elimₗ prop) ([↔]-elimᵣ([∩]-containment{s₂}{s₃}{x}) ([∧]-elimᵣ prop)))) :of: ((x ∈ s₁)∧((x ∈ s₂)∧(x ∈ s₃)) ← (x ∈ s₁)∧(x ∈ (s₂ ∩ s₃))))
        ∘ (([↔]-elimᵣ([∩]-containment{s₁}{s₂ ∩ s₃}{x}))                                                   :of: ((x ∈ s₁)∧(x ∈ (s₂ ∩ s₃)) ← (x ∈ (s₁ ∩ (s₂ ∩ s₃)))))

      r : (x ∈ ((s₁ ∩ s₂) ∩ s₃)) → (x ∈ (s₁ ∩ (s₂ ∩ s₃)))
      r = (([↔]-elimₗ([∩]-containment{s₁}{s₂ ∩ s₃}{x}))                                                   :of: ((x ∈ s₁)∧(x ∈ (s₂ ∩ s₃)) → (x ∈ (s₁ ∩ (s₂ ∩ s₃)))))
        ∘ ((prop ↦ ([∧]-intro ([∧]-elimₗ prop) ([↔]-elimₗ([∩]-containment{s₂}{s₃}{x}) ([∧]-elimᵣ prop)))) :of: ((x ∈ s₁)∧((x ∈ s₂)∧(x ∈ s₃)) → (x ∈ s₁)∧(x ∈ (s₂ ∩ s₃))))
        ∘ ([↔]-elimᵣ [∧]-associativity)
        ∘ ((prop ↦ ([∧]-intro ([↔]-elimᵣ([∩]-containment{s₁}{s₂}{x}) ([∧]-elimₗ prop)) ([∧]-elimᵣ prop))) :of: ((x ∈ (s₁ ∩ s₂))∧(x ∈ s₃) → ((x ∈ s₁)∧(x ∈ s₂))∧(x ∈ s₃)))
        ∘ (([↔]-elimᵣ([∩]-containment{s₁ ∩ s₂}{s₃}{x}))                                                   :of: ((x ∈ ((s₁ ∩ s₂) ∩ s₃)) → (x ∈ (s₁ ∩ s₂))∧(x ∈ s₃)))

module NaturalNumbers where
  open Axioms1
  open Operations

  module _ ⦃ _ : EmptySetExistence ⦄ where
    -- Could be interpreted as a set theoretic definition of zero from the natural numbers.
    𝟎 : S
    𝟎 = ∅

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    -- Could be interpreted as a set theoretic definition of the successor function from the natural numbers.
    𝐒 : S → S
    𝐒(x) = (x ∪ •(x))

  module _ ⦃ _ : EmptySetExistence ⦄ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    Inductive : S → Stmt
    Inductive(N) = ((𝟎 ∈ N) ∧ (∀{n} → (n ∈ N) → (𝐒(n) ∈ N)))

module Tuples where
  open Axioms1
  open Operations
  open Relations

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    _,_ : S → S → S
    _,_ x y = (x ∪ (x ⟒ y))

    postulate Tuple-elem-uniqueness : ∀{x₁ x₂ y₁ y₂} → ((x₁ , y₁) ≡ (x₂ , y₂)) → (x₁ ≡ x₂)∧(y₁ ≡ y₂)
    -- Tuple-elem-uniqueness (x1y1x2y2) =

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ ⦃ _ : RestrictedComprehensionExistence ⦄ ⦃ _ : PowerSetExistence ⦄ where
    _⨯_ : S → S → S
    _⨯_ s₁ s₂ = filter(℘(℘(s₁ ∪ s₂))) (s ↦ ∃(x ↦ ∃(y ↦ (x ∈ s₁) ∧ (y ∈ s₂) ∧ (s ≡ (x , y)))))

module Functions where
  open Axioms1
  open Operations
  open Relations
  open Tuples

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    Function : S → S → S → Stmt
    Function(f) (s₁)(s₂) = (∀{x} → (x ∈ s₁) → ∃(y ↦ (y ∈ s₂) ∧ ((x , y) ∈ f) ∧ (∀{y₂} → ((x , y₂) ∈ f) → (y ≡ y₂))))

  module _ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ ⦃ _ : RestrictedComprehensionExistence ⦄ ⦃ _ : PowerSetExistence ⦄ where
    _^_ : S → S → S
    _^_ s₁ s₂ = filter(℘(s₂ ⨯ s₁)) (f ↦ Function(f)(s₁)(s₂))

module Axioms2 where
  open Axioms1
  open NaturalNumbers
  open Relations

  module _ ⦃ _ : EmptySetExistence ⦄ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ where
    -- Sets can model ℕ.
    -- This can be used to construct a set representing the natural numbers.
    -- In this context, "Model" and "Representing" means a bijection.
    record InfinityAxiom : Set(Lvl.𝟎) where
      field infinity : ∃(N ↦ Inductive(N))
    open InfinityAxiom ⦃ ... ⦄ public

  record ChoiceAxiom : Set(Lvl.𝟎) where
    field choice : ⊤
  open ChoiceAxiom ⦃ ... ⦄ public

module NaturalNumberTheorems where
  open Axioms1
  open Axioms2
  open NaturalNumbers
  open Operations
  open OperationsTheorems
  open Relations
  open RelationsTheorems

  module _ ⦃ _ : EmptySetExistence ⦄ ⦃ _ : UnionExistence ⦄ ⦃ _ : PairExistence ⦄ ⦃ _ : InfinityAxiom ⦄ ⦃ _ : RestrictedComprehensionExistence ⦄ where
    -- TODO: I think a filtering like this gives the minimal inductive set?
    ℕ : S
    ℕ = filter([∃]-extract(infinity)) (n ↦ (n ≡ 𝟎) ∨ ∃(y ↦ n ≡ 𝐒(y)))

    [ℕ]-containment-in-infinity : ∀{n} → (n ∈ ℕ) → (n ∈ [∃]-extract(infinity))
    [ℕ]-containment-in-infinity {n} (n-containment) = [∧]-elimₗ (([↔]-elimᵣ (filter-containment {_}{_}{n})) (n-containment))

    [ℕ]-contains-[𝟎] : (𝟎 ∈ ℕ)
    [ℕ]-contains-[𝟎] = ([↔]-elimₗ (filter-containment {_}{_}{𝟎})) ([∧]-intro in-infinity satisfy-property) where
       in-infinity : 𝟎 ∈ [∃]-extract(infinity)
       in-infinity = [∧]-elimₗ ([∃]-property(infinity))

       satisfy-property : (𝟎 ≡ 𝟎) ∨ ∃(y ↦ 𝟎 ≡ 𝐒(y))
       satisfy-property = [∨]-introₗ [≡]-reflexivity

    [ℕ]-contains-[𝐒] : ∀{n} → (n ∈ ℕ) → (𝐒(n) ∈ ℕ)
    [ℕ]-contains-[𝐒] {n} (n-containment) = ([↔]-elimₗ (filter-containment {_}{_}{𝐒(n)})) ([∧]-intro in-infinity satisfy-property) where
      in-infinity : (𝐒(n) ∈ [∃]-extract(infinity))
      in-infinity = [∧]-elimᵣ ([∃]-property(infinity)) {n} ([ℕ]-containment-in-infinity {n} (n-containment))

      satisfy-property : (𝐒(n) ≡ 𝟎) ∨ ∃(y ↦ 𝐒(n) ≡ 𝐒(y))
      satisfy-property = [∨]-introᵣ ([∃]-intro n [≡]-reflexivity)

    -- TODO: Is this even provable without extensionality and with ℕ defined like this?
    -- [ℕ]-contains : ∀{n} → (n ∈ ℕ) ← (n ≡ 𝟎)∨(∃(x ↦ n ≡ 𝐒(x)))
    -- [ℕ]-contains {_} ([∨]-introₗ [≡]-intro) = [ℕ]-contains-[𝟎]
    -- [ℕ]-contains {n} ([∨]-introᵣ ([∃]-intro (x) ([≡]-intro))) = [ℕ]-contains-[𝐒] {n} [≡]-intro

    [ℕ]-contains-only : ∀{n} → (n ∈ ℕ) → (n ≡ 𝟎)∨(∃(x ↦ n ≡ 𝐒(x)))
    [ℕ]-contains-only {n} (n-containment) = [∧]-elimᵣ (([↔]-elimᵣ (filter-containment {_}{_}{n})) (n-containment))

    [ℕ]-subset : ∀{Nₛ} → Inductive(Nₛ) → (ℕ ⊆ Nₛ)
    [ℕ]-subset {Nₛ} ([∧]-intro zero-containment successor-containment) {n} ([ℕ]-n-containment) =
      [∨]-elim (zero) (succ) ([ℕ]-contains-only{n} ([ℕ]-n-containment)) where

      postulate zero : (n ≡ 𝟎) → (n ∈ Nₛ)
      postulate succ : (∃(x ↦ n ≡ 𝐒(x))) → (n ∈ Nₛ)

    [ℕ]-set-induction : ∀{Nₛ} → (Nₛ ⊆ ℕ) → Inductive(Nₛ) → (Nₛ ≡ ℕ)
    [ℕ]-set-induction {Nₛ} (Nₛ-subset) (ind) = [↔]-intro ([ℕ]-subset {Nₛ} (ind)) (Nₛ-subset)

    [ℕ]-induction : ∀{φ} → φ(𝟎) → (∀{n} → (n ∈ ℕ) → φ(n) → φ(𝐒(n))) → (∀{n} → (n ∈ ℕ) → φ(n))
    [ℕ]-induction {φ} (zero) (succ) {n} (n-in-ℕ) =
      ([∧]-elimᵣ
        (([↔]-elimᵣ filter-containment)
          ([ℕ]-subset {filter(ℕ)(φ)} ([∧]-intro (zero-in) (succ-in)) {n} (n-in-ℕ))
        )
      ) where

      module _ {n} (n-in-ℕ : n ∈ ℕ) where
        n-inₗ : φ(n) ← (n ∈ filter(ℕ)(φ))
        n-inₗ (proof) = [∧]-elimᵣ (([↔]-elimᵣ filter-containment) (proof))

        n-inᵣ : φ(n) → (n ∈ filter(ℕ)(φ))
        n-inᵣ (proof) = ([↔]-elimₗ filter-containment) ([∧]-intro (n-in-ℕ) (proof))

        Sn-inₗ : φ(𝐒(n)) ← (𝐒(n) ∈ filter(ℕ)(φ))
        Sn-inₗ (proof) = [∧]-elimᵣ (([↔]-elimᵣ filter-containment) (proof))

        Sn-inᵣ : φ(𝐒(n)) → (𝐒(n) ∈ filter(ℕ)(φ))
        Sn-inᵣ (proof) = ([↔]-elimₗ filter-containment) ([∧]-intro ([ℕ]-contains-[𝐒] (n-in-ℕ)) (proof))

      zero-in : 𝟎 ∈ filter(ℕ)(φ)
      zero-in = ([↔]-elimₗ filter-containment) ([∧]-intro ([ℕ]-contains-[𝟎]) (zero))

      postulate succ-in : ∀{n} → (n ∈ filter(ℕ)(φ)) → (𝐒(n) ∈ filter(ℕ)(φ))
      -- succ-in = (Sn-inᵣ) ∘ (succ {n} (n-in-ℕ)) ∘ (n-inₗ)

    -- TODO: Is it possible to connect this to the ℕ in Numeral.Natural.ℕ?

    -- TODO: Is (∀{s₁ s₂ : S} → (s₁ ≡ s₂) → (s₁ ∈ S) → (s₂ ∈ S)) provable without axiom of extensionality?

record IZF : Set(Lvl.𝐒(Lvl.𝟎)) where
  instance constructor IZFStructure
  open Axioms1
  open Axioms2

  field
    ⦃ empty ⦄         : EmptySetExistence
    ⦃ pair ⦄          : PairExistence
    ⦃ union ⦄         : UnionExistence
    ⦃ power ⦄         : PowerSetExistence
    ⦃ comprehension ⦄ : RestrictedComprehensionExistence
    ⦃ infinity ⦄      : InfinityAxiom
    ⦃ collection ⦄    : CollectionAxiom
    ⦃ induction ⦄     : InductionProof
