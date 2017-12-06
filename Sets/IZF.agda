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

  [⊆]-reflexivity : ∀{s} → (s ⊆ s)
  [⊆]-reflexivity = [→]-reflexivity

  [⊆]-transitivity : ∀{s₁ s₂ s₃} → (s₁ ⊆ s₂) → (s₂ ⊆ s₃) → (s₁ ⊆ s₃)
  [⊆]-transitivity(s12)(s23){x} = [→]-transitivity(s12{x})(s23{x})

  [⊆]-antisymmetry : ∀{s₁ s₂} → (s₁ ⊇ s₂) → (s₁ ⊆ s₂) → (s₁ ≡ s₂)
  [⊆]-antisymmetry(s21)(s12){x} = [↔]-intro (s21{x}) (s12{x})

module Axioms1 where
  open Relations

  -- A set which is empty exists.
  record EmptySetAxiom : Set(Lvl.𝟎) where
    field empty : ∃(s ↦ Empty(s))
  open EmptySetAxiom ⦃ ... ⦄ public

  -- A set with two elements exists.
  record PairingAxiom : Set(Lvl.𝟎) where
    field pair : ∀{x₁ x₂} → ∃(s ↦ Pair(s)(x₁)(x₂))
  open PairingAxiom ⦃ ... ⦄ public

  -- A set which contains all the elements of a group of sets exists.
  record UnionAxiom : Set(Lvl.𝟎) where
    field union : ∀{ss} → ∃(sᵤ ↦ UnionAll(sᵤ)(ss))
  open UnionAxiom ⦃ ... ⦄ public

  -- A set which contains all the subsets of a set exists.
  record PowerSetAxiom : Set(Lvl.𝟎) where
    field power : ∀{s} → ∃(sₚ ↦ Power(sₚ)(s))
  open PowerSetAxiom ⦃ ... ⦄ public

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  record ComprehensionAxiom : Set(Lvl.𝐒(Lvl.𝟎)) where
    field comprehension : ∀{s}{φ : S → Stmt} → ∃(sₛ ↦ FilteredSubset(sₛ)(s)(φ))
  open ComprehensionAxiom ⦃ ... ⦄ public

  -- ??
  record CollectionAxiom : Set(Lvl.𝐒(Lvl.𝟎)) where
    field collection : ∀{φ : S → S → Stmt} → ∀{a} → (∀{x} → (x ∈ a) → ∃(y ↦ φ(x)(y))) → ∃(b ↦ ∀{x} → (x ∈ a) → ∃(y ↦ ((y ∈ b) ∧ φ(x)(y))))
  open CollectionAxiom ⦃ ... ⦄ public

  -- Induction proof on sets.
  -- This can be used to prove stuff about all sets.
  -- This can be interpreted as:
  --   A proof of a predicate satisfying every element of an arbitrary set is a proof of this predicate satisfying every set.
  record InductionAxiom : Set(Lvl.𝐒(Lvl.𝟎)) where
    field induction : ∀{φ : S → Stmt} → (∀{s} → (∀{x} → (x ∈ s) → φ(x)) → φ(s)) → (∀{s} → φ(s))
  open InductionAxiom ⦃ ... ⦄

module Theorems1 where
  open Axioms1
  open Relations

  module _ ⦃ _ : PairingAxiom ⦄ where
      -- A set with only one element exists.
    single : ∀{x₁} → ∃(s ↦ (∀{x} → (x ∈ s) ↔ (x ≡ x₁)))
    single{x} with pair{x}{x}
    ...          | [∃]-intro (z) (f) = ([∃]-intro (z) (\{w} → [↔]-transitivity (f{w}) [∨]-redundancy))

  module _ ⦃ _ : EmptySetAxiom ⦄ where
    [∅]-uniqueness : ∀{x y} → Empty(x) → Empty(y) → (x ≡ y)
    [∅]-uniqueness (empty-x)(empty-y) =
      ([↔]-intro
        ([⊥]-elim ∘ empty-y)
        ([⊥]-elim ∘ empty-x)
      )

module Operations where
  open Axioms1
  open Relations
  open Theorems1

  module _ ⦃ _ : EmptySetAxiom ⦄ where
    -- Definition of the empty set: ∅={}.
    -- This can be used to construct a set with no elements.
    ∅ : S
    ∅ = [∃]-extract(empty)

  module _ ⦃ _ : PairingAxiom ⦄ where
    -- Definition of a singleton set: {x} for some element x.
    -- This can be used to construct a set with a single element.
    • : S → S
    •(x) = [∃]-extract(single{x})

    -- Definition of a pair set: {x,y} for some elements x and y.
    -- This can be used to construct a set with a countable number of elements: x⟒y⟒z.
    _⟒_ : S → S → S
    _⟒_ (x)(y) = [∃]-extract(pair{x}{y})

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    -- Definition of the union of two sets: s₁∪s₂ for two sets s₁ and s₂
    -- This can be used to construct a set that contains all elements from either of the two sets.
    _∪_ : S → S → S
    _∪_ s₁ s₂ = [∃]-extract(union{s₁ ⟒ s₂})

  module _ ⦃ _ : UnionAxiom ⦄ where
    -- Definition of the union of a set of sets: ⋃(ss) for a set of sets ss
    -- This can be used to construct a set that contains all elements from the sets.
    reduce-[∪] : S → S
    reduce-[∪] ss = [∃]-extract(union{ss})

  module _ ⦃ _ : PowerSetAxiom ⦄ where
    -- Definition of the power set of a set: ℘(s) for some set s
    -- This can be used to construct a set that contains all subsets of a set.
    ℘ : S → S
    ℘(s) = [∃]-extract(power{s})

  module _ ⦃ _ : ComprehensionAxiom ⦄ where
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

module OperationsTheorems where
  open Axioms1
  open Operations
  open Relations
  open Theorems1
  open Relations
  open RelationsTheorems

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Containment

  module _ ⦃ _ : EmptySetAxiom ⦄ where
    [∅]-containment : Empty(∅)
    [∅]-containment = [∃]-property(empty)

  module _ ⦃ _ : PairingAxiom ⦄ where
    [•]-containment : ∀{x₁} → (x₁ ∈ •(x₁))
    [•]-containment{x₁} = [↔]-elimₗ([∃]-property(single{x₁})) ([≡]-reflexivity)

    [⟒]-containment : ∀{x₁ x₂}{x} → (x ∈ (x₁ ⟒ x₂)) ↔ (x ≡ x₁)∨(x ≡ x₂)
    [⟒]-containment{x₁}{x₂} = [∃]-property(pair{x₁}{x₂})

    [⟒]-containmentₗ : ∀{x₁ x₂} → (x₁ ∈ (x₁ ⟒ x₂))
    [⟒]-containmentₗ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introₗ([≡]-reflexivity))

    [⟒]-containmentᵣ : ∀{x₁ x₂} → (x₂ ∈ (x₁ ⟒ x₂))
    [⟒]-containmentᵣ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introᵣ([≡]-reflexivity))

  module _ ⦃ _ : ComprehensionAxiom ⦄ where
    filter-containment : ∀{s}{φ}{x} → (x ∈ filter(s)(φ)) ↔ ((x ∈ s) ∧ φ(x))
    filter-containment{s} = [∃]-property(comprehension)

    [∩]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∩ s₂)) ↔ (x ∈ s₁)∧(x ∈ s₂)
    [∩]-containment = filter-containment

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    [∪]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ↔ (x ∈ s₁)∨(x ∈ s₂)
    [∪]-containment = [↔]-intro [∪]-containmentₗ [∪]-containmentᵣ where
      postulate [∪]-containmentₗ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ← (x ∈ s₁)∨(x ∈ s₂)
      postulate [∪]-containmentᵣ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) → (x ∈ s₁)∨(x ∈ s₂)

  module _ ⦃ _ : PowerSetAxiom ⦄ where
    [℘]-containment : ∀{s sₛ} → (sₛ ⊆ s) ↔ (sₛ ∈ ℘(s))
    [℘]-containment{s} = [↔]-symmetry([∃]-property(power{s}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Subset

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    [∪]-subsetₗ : ∀{s₁ s₂} → (s₁ ⊆ (s₁ ∪ s₂))
    [∪]-subsetₗ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introₗ

    [∪]-subsetᵣ : ∀{s₁ s₂} → (s₂ ⊆ (s₁ ∪ s₂))
    [∪]-subsetᵣ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introᵣ

    postulate [∪]-subset-eq : ∀{s₁ s₂ s₃} → ((s₁ ∪ s₂) ⊆ s₃) ↔ ((s₁ ⊆ s₃)∧(s₂ ⊆ s₃))

  module _ ⦃ _ : ComprehensionAxiom ⦄ where
    [∩]-subsetₗ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₁)
    [∩]-subsetₗ = [∧]-elimₗ ∘ ([↔]-elimᵣ([∩]-containment))

    [∩]-subsetᵣ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₂)
    [∩]-subsetᵣ = [∧]-elimᵣ ∘ ([↔]-elimᵣ([∩]-containment))

    filter-subset : ∀{s}{φ} → (filter(s)(φ) ⊆ s)
    filter-subset{s}{φ} {x}(x∈s) = [∧]-elimₗ([↔]-elimᵣ([∃]-property(comprehension{s}{φ}))(x∈s))

  module _ ⦃ _ : PowerSetAxiom ⦄ where
   postulate [℘]-subset : ∀{s₁ s₂} → (s₁ ⊆ s₂) → (℘(s₁) ⊆ ℘(s₂))


  -- TODO: Does this hold: Empty(s) ∨ NonEmpty(s) ? Probably not

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Commutativity

  -- [⟒]-commutativity : ∀{s₁ s₂} → (s₁ ⟒ s₂) ≡ (s₂ ⟒ s₁)
  -- [⟒]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
  --   f : ∀{s₁ s₂} → (x ∈ (s₁ ⟒ s₂)) → (x ∈ (s₂ ⟒ s₁))
  --   f{s₁}{s₂} = ([↔]-elimₗ([⟒]-containment{s₂}{s₁}{x})) ∘ ([∨]-symmetry) ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    [∪]-commutativity : ∀{s₁ s₂} → (s₁ ∪ s₂) ≡ (s₂ ∪ s₁)
    [∪]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
      f : ∀{s₁ s₂} → (x ∈ (s₁ ∪ s₂)) → (x ∈ (s₂ ∪ s₁))
      f{s₁}{s₂} =
        ([↔]-elimₗ([∪]-containment{s₂}{s₁}{x}))
        ∘ ([∨]-symmetry)
        ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  module _ ⦃ _ : ComprehensionAxiom ⦄ where
    [∩]-commutativity : ∀{s₁ s₂} → (s₁ ∩ s₂) ≡ (s₂ ∩ s₁)
    [∩]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
      f : ∀{s₁ s₂} → (x ∈ (s₁ ∩ s₂)) → (x ∈ (s₂ ∩ s₁))
      f{s₁}{s₂} =
        ([↔]-elimₗ([∩]-containment{s₂}{s₁}{x}))
        ∘ ([∧]-symmetry)
        ∘ ([↔]-elimᵣ([∩]-containment{s₁}{s₂}{x}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Associativity

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
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

  module _ ⦃ _ : ComprehensionAxiom ⦄ where
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

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Other

  module _ ⦃ _ : EmptySetAxiom ⦄ where
    [∅]-in-subset : ∀{s} → (∅ ⊆ s)
    [∅]-in-subset = [⊥]-elim ∘ [∅]-containment

  module _ ⦃ _ : EmptySetAxiom ⦄ ⦃ _ : PowerSetAxiom ⦄ where
    [℘][∅]-containment : ∀{s} → (∅ ∈ ℘(s))
    [℘][∅]-containment = [↔]-elimᵣ([℘]-containment)([∅]-in-subset)

  module _ ⦃ _ : PowerSetAxiom ⦄ where
    [℘]-set-containment : ∀{s} → (s ∈ ℘(s))
    [℘]-set-containment = [↔]-elimᵣ([℘]-containment)([⊆]-reflexivity)

  -- TODO: Is this provable?
  -- self-containment : ∀{s} → ¬(s ∈ s) -- ¬ ∃(s ↦ s ∈ s)
  -- self-containment = 

module NaturalNumbers where
  open Axioms1
  open Operations

  module _ ⦃ _ : EmptySetAxiom ⦄ where
    -- Could be interpreted as a set theoretic definition of zero from the natural numbers.
    𝟎 : S
    𝟎 = ∅

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    -- Could be interpreted as a set theoretic definition of the successor function from the natural numbers.
    𝐒 : S → S
    𝐒(x) = (x ∪ •(x))

module Tuples where
  open Axioms1
  open Operations

  module _ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    _,_ : S → S → S
    _,_ x y = (x ∪ (x ⟒ y))

  -- _⨯_ : S → S → S
  -- _⨯_ s₁ s₂ = 

{-
  Singleton-elem-uniqueness : ∀{x y₁ y₂} → (y₁ ∈ Singleton(x)) → (y₂ ∈ Singleton(x)) → (y₁ ≡ y₂)
  Singleton-elem-uniqueness (y₁-proof)(y₂-proof) =
    ([↔]-intro
      (y₁-proof)
      (y₂-proof)
    )
-}

module Axioms2 where
  open Axioms1
  open NaturalNumbers
  open Relations

  module _ ⦃ _ : EmptySetAxiom ⦄ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ where
    -- Sets can model ℕ.
    -- This can be used to construct a set representing the natural numbers.
    record InfinityAxiom : Set(Lvl.𝟎) where
      field infinity : ∃(N ↦ ((𝟎 ∈ N) ∧ (∀{n} → (n ∈ N) → (𝐒(n) ∈ N))))
    open InfinityAxiom ⦃ ... ⦄ public

  record ChoiceAxiom : Set(Lvl.𝟎) where
    field choice : ⊤
  open ChoiceAxiom ⦃ ... ⦄ public

module NaturalNumberTheorems where
  open Axioms1
  open Axioms2
  open NaturalNumbers
  open Relations

  module _ ⦃ _ : EmptySetAxiom ⦄ ⦃ _ : UnionAxiom ⦄ ⦃ _ : PairingAxiom ⦄ ⦃ _ : InfinityAxiom ⦄ where
    ℕ = [∃]-extract(infinity) -- TODO: This is not an unique set as it is currently defined (What did I mean when I wrote this?)

    [ℕ]-contains-[𝟎] : (𝟎 ∈ ℕ)
    [ℕ]-contains-[𝟎] = [∧]-elimₗ ([∃]-property(infinity))

    [ℕ]-contains-[𝐒] : ∀{n} → (n ∈ ℕ) → (𝐒(n) ∈ ℕ)
    [ℕ]-contains-[𝐒] = [∧]-elimᵣ ([∃]-property(infinity))

    postulate [ℕ]-induction : ∀{Nₛ} → (Nₛ ⊆ ℕ) → (𝟎 ∈ Nₛ) → (∀{n} → (n ∈ Nₛ) → (𝐒(n) ∈ Nₛ)) → (Nₛ ≡ ℕ)

    postulate [ℕ]-contains-only : ∀{n} → (n ∈ ℕ) → (n ≡ 𝟎)∨(∃(x ↦ n ≡ 𝐒(x)))

record IZF : Set(Lvl.𝐒(Lvl.𝟎)) where
  instance constructor IZFStructure
  open Axioms1
  open Axioms2

  field
    ⦃ empty ⦄         : EmptySetAxiom
    ⦃ pair ⦄          : PairingAxiom
    ⦃ union ⦄         : UnionAxiom
    ⦃ power ⦄         : PowerSetAxiom
    ⦃ comprehension ⦄ : ComprehensionAxiom
    ⦃ infinity ⦄      : InfinityAxiom
    ⦃ collection ⦄    : CollectionAxiom
    ⦃ induction ⦄     : InductionAxiom
