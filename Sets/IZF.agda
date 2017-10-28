import      Lvl
open import Functional
open import Logic.Propositional{Lvl.𝟎}
open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
open import Logic.Theorems{Lvl.𝟎}
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
  Empty(s) = (∀{x} → ¬(x ∈ s))

  -- The statement that the set s is non-empty
  NonEmpty : S → Stmt
  NonEmpty(s) = ∃(x ↦ (x ∈ s))

module RelationsTheorems where
  open Relations

  [≡]-reflexivity : ∀{s} → (s ≡ s)
  [≡]-reflexivity = [↔]-reflexivity

  [≡]-transitivity : ∀{s₁ s₂ s₃} → (s₁ ≡ s₂) → (s₂ ≡ s₃) → (s₁ ≡ s₃)
  [≡]-transitivity(s12)(s23){x} = [↔]-transitivity(s12{x})(s23{x})

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
    separation : ∀{s}{φ : S → Stmt} → ∃(sₛ ↦ (∀{x} → (x ∈ sₛ) ↔ ((x ∈ s) ∧ φ(x))))

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

  -- Definition of the usual "set builder notation": {x∊s. φ(x)} for some set s
  -- This can be used to construct a set that is the subset which satisfies a certain predicate for every element.
  subset : S → (S → Stmt) → S
  subset(s)(φ) = [∃]-extract(separation{s}{φ})

  -- Definition of the intersection of two sets: s₁∩s₂ for two sets s₁ and s₂
  -- This can be used to construct a set that contains all elements that only are in both sets.
  _∩_ : S → S → S
  _∩_ (s₁)(s₂) = subset(s₁)(x ↦ (x ∈ s₂))

  -- Definition of the intersection of a set of sets: ⋃(ss) for a set of sets ss
  -- This can be used to construct a set that contains all elements that only are in all of the sets.
  -- reduce-[∪] : S → S
  -- reduce-[∪] ss = subset(s₁)(x ↦ (x ∈ s₂))

  _∖_ : S → S → S
  _∖_ (s₁)(s₂) = subset(s₁)(_∉ s₂)

module OperationsTheorems ⦃ _ : ConstructionAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open ConstructionTheorems
  open Operations
  open Relations
  open RelationsTheorems

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Containment

  [∅]-containment : Empty(∅)
  [∅]-containment = [∃]-property(empty)

  [•]-containment : ∀{x₁} → (x₁ ∈ •(x₁))
  [•]-containment{x₁} = [↔]-elimₗ([∃]-property(single{x₁})) ([≡]-reflexivity)

  [⟒]-containment : ∀{x₁ x₂}{x} → (x ∈ (x₁ ⟒ x₂)) ↔ (x ≡ x₁)∨(x ≡ x₂)
  [⟒]-containment{x₁}{x₂} = [∃]-property(pair{x₁}{x₂})

  [⟒]-containmentₗ : ∀{x₁ x₂} → (x₁ ∈ (x₁ ⟒ x₂))
  [⟒]-containmentₗ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introₗ([≡]-reflexivity))

  [⟒]-containmentᵣ : ∀{x₁ x₂} → (x₂ ∈ (x₁ ⟒ x₂))
  [⟒]-containmentᵣ{x₁}{x₂} = [↔]-elimₗ([∃]-property(pair{x₁}{x₂})) ([∨]-introᵣ([≡]-reflexivity))

  subset-containment : ∀{s}{φ}{x} → (x ∈ subset(s)(φ)) ↔ ((x ∈ s) ∧ φ(x))
  subset-containment{s} = [∃]-property(separation)

  [∪]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ↔ (x ∈ s₁)∨(x ∈ s₂)
  [∪]-containment = [↔]-intro [∪]-containmentₗ [∪]-containmentᵣ where
    postulate [∪]-containmentₗ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) ← (x ∈ s₁)∨(x ∈ s₂)
    postulate [∪]-containmentᵣ : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∪ s₂)) → (x ∈ s₁)∨(x ∈ s₂)

  [∩]-containment : ∀{s₁ s₂}{x} → (x ∈ (s₁ ∩ s₂)) ↔ (x ∈ s₁)∧(x ∈ s₂)
  [∩]-containment = subset-containment

  [℘]-containment : ∀{s sₛ} → (sₛ ⊆ s) ↔ (sₛ ∈ ℘(s))
  [℘]-containment{s} = [↔]-commutativity([∃]-property(power{s}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Subset

  [∪]-subsetₗ : ∀{s₁ s₂} → (s₁ ⊆ (s₁ ∪ s₂))
  [∪]-subsetₗ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introₗ

  [∪]-subsetᵣ : ∀{s₁ s₂} → (s₂ ⊆ (s₁ ∪ s₂))
  [∪]-subsetᵣ = ([↔]-elimₗ([∪]-containment)) ∘ [∨]-introᵣ

  [∩]-subsetₗ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₁)
  [∩]-subsetₗ = [∧]-elimₗ ∘ ([↔]-elimᵣ([∩]-containment))

  [∩]-subsetᵣ : ∀{s₁ s₂} → ((s₁ ∩ s₂) ⊆ s₂)
  [∩]-subsetᵣ = [∧]-elimᵣ ∘ ([↔]-elimᵣ([∩]-containment))

  postulate [℘]-subset : ∀{s₁ s₂} → (s₁ ⊆ s₂) → (℘(s₁) ⊆ ℘(s₂))

  subset-subset : ∀{s}{φ} → (subset(s)(φ) ⊆ s)
  subset-subset{s}{φ} {x}(x∈s) = [∧]-elimₗ([↔]-elimᵣ([∃]-property(separation{s}{φ}))(x∈s))

  -- TODO: Does this hold: Empty(s) ∨ NonEmpty(s) ? Probably not

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Commutativity

  -- [⟒]-commutativity : ∀{s₁ s₂} → (s₁ ⟒ s₂) ≡ (s₂ ⟒ s₁)
  -- [⟒]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
  --   f : ∀{s₁ s₂} → (x ∈ (s₁ ⟒ s₂)) → (x ∈ (s₂ ⟒ s₁))
  --   f{s₁}{s₂} = ([↔]-elimₗ([⟒]-containment{s₂}{s₁}{x})) ∘ ([∨]-commutativity) ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  [∪]-commutativity : ∀{s₁ s₂} → (s₁ ∪ s₂) ≡ (s₂ ∪ s₁)
  [∪]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
    f : ∀{s₁ s₂} → (x ∈ (s₁ ∪ s₂)) → (x ∈ (s₂ ∪ s₁))
    f{s₁}{s₂} =
      ([↔]-elimₗ([∪]-containment{s₂}{s₁}{x}))
      ∘ ([∨]-commutativity)
      ∘ ([↔]-elimᵣ([∪]-containment{s₁}{s₂}{x}))

  [∩]-commutativity : ∀{s₁ s₂} → (s₁ ∩ s₂) ≡ (s₂ ∩ s₁)
  [∩]-commutativity{s₁}{s₂} {x} = [↔]-intro (f{s₂}{s₁}) (f{s₁}{s₂}) where
    f : ∀{s₁ s₂} → (x ∈ (s₁ ∩ s₂)) → (x ∈ (s₂ ∩ s₁))
    f{s₁}{s₂} =
      ([↔]-elimₗ([∩]-containment{s₂}{s₁}{x}))
      ∘ ([∧]-commutativity)
      ∘ ([↔]-elimᵣ([∩]-containment{s₁}{s₂}{x}))

  -- -- -- -- -- -- -- -- -- -- -- -- -- --
  -- Associativity

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

  [∅]-in-subset : ∀{s} → (∅ ⊆ s)
  [∅]-in-subset = [⊥]-elim ∘ [∅]-containment

  [℘][∅]-containment : ∀{s} → (∅ ∈ ℘(s))
  [℘][∅]-containment = [↔]-elimᵣ([℘]-containment)([∅]-in-subset)

  -- TODO: Is this provable?
  -- self-containment : ∀{s} → ¬(s ∈ s) -- ¬ ∃(s ↦ s ∈ s)
  -- self-containment = 

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
    -- This can be used to construct a set representing the natural numbers.
    infinity : ∃(N ↦ ((∅ ∈ N) ∧ (∀{n} → (n ∈ N) → (𝐒(n) ∈ N))))

    -- ??
    collection : ∀{φ : S → S → Stmt} → ∀{a} → (∀{x} → (x ∈ a) → ∃(y ↦ φ(x)(y))) → ∃(b ↦ ∀{x} → (x ∈ a) → ∃(y ↦ ((y ∈ b) ∧ φ(x)(y))))

    -- Induction proof on sets.
    -- This can be used to prove stuff about all sets.
    -- This can be interpreted as:
    --   A proof of a predicate satisfying every element of an arbitrary set is a proof of this predicate satisfying every set.
    induction : ∀{φ : S → Stmt} → (∀{s} → (∀{x} → (x ∈ s) → φ(x)) → φ(s)) → (∀{s} → φ(s))

module Theorems ⦃ _ : ConstructionAxioms ⦄ ⦃ _ : ProofAxioms ⦄ where
  open ConstructionAxioms ⦃ ... ⦄
  open ProofAxioms ⦃ ... ⦄
  open Relations

  ℕ = [∃]-extract(infinity) -- TODO: This is not an unique set as it is currently defined (What did I mean when I wrote this?)

{-
  Singleton-elem-uniqueness : ∀{x y₁ y₂} → (y₁ ∈ Singleton(x)) → (y₂ ∈ Singleton(x)) → (y₁ ≡ y₂)
  Singleton-elem-uniqueness (y₁-proof)(y₂-proof) =
    ([↔]-intro
      (y₁-proof)
      (y₂-proof)
    )
-}
