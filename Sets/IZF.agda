import      Lvl
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Logic.Theorems{Lvl.𝟎}

-- Based on https://plato.stanford.edu/entries/set-theory-constructive/axioms-CZF-IZF.html (2017-10-13)
module Sets.IZF (S : Set(Lvl.𝟎)) (_∈_ : S → S → Stmt) where

module Relations where
  _⊆_ : S → S → Stmt
  _⊆_ a b = (∀{x} → (x ∈ a) → (x ∈ b))

  _⊇_ : S → S → Stmt
  _⊇_ a b = (∀{x} → (x ∈ a) ← (x ∈ b))

  _≡_ : S → S → Stmt
  _≡_ a b = (∀{x} → (x ∈ a) ↔ (x ∈ b))

  -- The statement that the set s is empty
  Empty : S → Stmt
  Empty(s) = (∀{x} → ¬(x ∈ s))

  -- The statement that the set s is non-empty
  NonEmpty : S → Stmt
  NonEmpty(s) = ∃(x ↦ (x ∈ s))

record ConstructionAxioms : Set(Lvl.𝐒(Lvl.𝟎)) where
  open Relations

  field
    -- A set which is empty exists.
    empty : ∃(x ↦ Empty(x))

    -- A set with two elements exists.
    pair : ∀{x₁ x₂} → ∃(s ↦ (∀{x} → (x ∈ s) ↔ (x ≡ x₁)∨(x ≡ x₂)))

    -- A set which contains all the elements of a group of sets exists.
    union : ∀{ss} → ∃(sᵤ ↦ (∀{x s} → (x ∈ sᵤ) ↔ (x ∈ s)∧(s ∈ ss)))

    -- A set which contains all the subsets of a set exists.
    power : ∀{s} → ∃(sₚ ↦ (∀{x} → (x ∈ sₚ) ↔ (x ⊆ s)))

    -- A set which is the subset of a set where all elements satisfies a predicate exists.
    separation : ∀{φ : S → Stmt} → ∀{a} → ∃(x ↦ (∀{y} → (y ∈ x) ↔ ((y ∈ a) ∧ φ(y))))

module ConstructionTheorems ⦃ _ : ConstructionAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open Relations

    -- A set with only one element exists.
  single : ∀{x₁} → ∃(s ↦ (∀{x} → (x ∈ s) ↔ (x ≡ x₁)))
  single{x} with pair{x}{x}
  ...          | [∃]-intro (z) (f) = ([∃]-intro (z) (\{w} → [↔]-transitivity (f{w}) [∨]-redundancy))

  [∅]-uniqueness : ∀{x y} → Empty(x) → Empty(y) → (x ≡ y)
  [∅]-uniqueness (empty-x)(empty-y) =
    ([↔]-intro
      ([⊥]-elim ∘ empty-y)
      ([⊥]-elim ∘ empty-x)
    )

module Operations ⦃ _ : ConstructionAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open ConstructionTheorems
  open Relations

  -- Definition of the empty set: ∅={}.
  -- This can be used to construct a set with no elements.
  ∅ : S
  ∅ = [∃]-extract(empty)

  -- Definition of a singleton set: {x} for some element x.
  -- This can be used to construct a set with a single element.
  • : S → S
  •(x) = [∃]-extract(single{x})

  -- Definition of a pair set: {x,y} for some elements x and y.
  -- This can be used to construct a set with a countable number of elements: x⟒y⟒z.
  _⟒_ : S → S → S
  _⟒_ (x)(y) = [∃]-extract(pair{x}{y})

  -- Definition of the union of two sets: s₁∪s₂ for two sets s₁ and s₂
  -- This can be used to construct a set that contains all elements from either of the two sets.
  _∪_ : S → S → S
  _∪_ s₁ s₂ = [∃]-extract(union{s₁ ⟒ s₂})

  -- Definition of the union of a set of sets: ⋃(ss) for a set of sets ss
  -- This can be used to construct a set that contains all elements from the sets.
  reduce-[∪] : S → S
  reduce-[∪] ss = [∃]-extract(union{ss})

  -- Definition of the power set of a set: ℘(s) for some set s
  -- This can be used to construct a set that contains all subsets of a set.
  ℘ : S → S
  ℘(s) = [∃]-extract(power{s})

  -- Definition of the usual "set builder notation": {x∈s. φ(x)} for some set s
  -- This can be used to construct a set that is the subset which satisfies a certain predicate for every element.
  subset : S → (S → Stmt) → S
  subset(s)(φ) = [∃]-extract(separation{φ}{s})

  -- Definition of the intersection of two sets: s₁∩s₂ for two sets s₁ and s₂
  -- This can be used to construct a set that contains all elements that only are in both sets.
  _∩_ : S → S → S
  _∩_ (s₁)(s₂) = subset(s₁)(x ↦ (x ∈ s₂))

  -- Definition of the intersection of a set of sets: ⋃(ss) for a set of sets ss
  -- This can be used to construct a set that contains all elements that only are in all of the sets.
  -- reduce-[∪] : S → S
  -- reduce-[∪] ss = subset(s₁)(x ↦ (x ∈ s₂))

module OperationsTheorems ⦃ _ : ConstructionAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open ConstructionTheorems
  open Operations
  open Relations

  postulate [∪]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ↔ (x ∈ s₁)∨(x ∈ s₂)

  postulate [∩]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∩ s₂)) ↔ (x ∈ s₁)∧(x ∈ s₂)

  postulate [∅]-containment : Empty(∅)

  postulate [∪]-subset : ∀{s₁ s₂} → (s₁ ⊆ (s₁ ∪ s₂))∧(s₂ ⊆ (s₁ ∪ s₂))

  postulate [∩]-subset : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₁)∧((s₁ ∪ s₂) ⊆ s₂)

  postulate [℘]-subset : ∀{s} → (s ⊆ ℘(s))

  postulate subset-subset : ∀{s}{φ} → (subset(s)(φ) ⊆ s)

  -- TODO: Does this hold: Empty(s) ∨ NonEmpty(s) ?

module NaturalNumbers ⦃ _ : ConstructionAxioms ⦄ where
  open Operations

  -- Could be interpreted as a set theoretic definition of zero from the natural numbers.
  𝟎 : S
  𝟎 = ∅

  -- Could be interpreted as a set theoretic definition of the successor function from the natural numbers.
  𝐒 : S → S
  𝐒(x) = (x ∪ •(x))

module Tuples ⦃ _ : ConstructionAxioms ⦄ where
  open Operations

  _,_ : S → S → S
  _,_ x y = (x ∪ (x ⟒ y))

  -- _⨯_ : S → S → S
  -- _⨯_ s₁ s₂ = 

record ProofAxioms ⦃ _ : ConstructionAxioms ⦄ : Set(Lvl.𝐒(Lvl.𝟎)) where
  open NaturalNumbers
  open Operations
  open Relations

  field
    -- Sets can model ℕ.
    infinity : ∃(N ↦ ((∅ ∈ N) ∧ (∀{n} → (n ∈ N) → (𝐒(n) ∈ N))))

    -- ??
    collection : ∀{φ : S → S → Stmt} → ∀{a} → (∀{x} → (x ∈ a) → ∃(y ↦ φ(x)(y))) → ∃(b ↦ ∀{x} → (x ∈ a) → ∃(y ↦ ((y ∈ b) ∧ φ(x)(y))))

    -- ??
    induction : ∀{φ : S → Stmt} → (∀{a} → (∀{y} → (y ∈ a) → φ(y)) → φ(a)) → (∀{a} → φ(a))

module Theorems ⦃ _ : ConstructionAxioms ⦄ ⦃ _ : ProofAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open ProofAxioms ⦃ ... ⦄
  open Relations

{-
  Singleton-elem-uniqueness : ∀{x y₁ y₂} → (y₁ ∈ Singleton(x)) → (y₂ ∈ Singleton(x)) → (y₁ ≡ y₂)
  Singleton-elem-uniqueness (y₁-proof)(y₂-proof) =
    ([↔]-intro
      (y₁-proof)
      (y₂-proof)
    )
-}
