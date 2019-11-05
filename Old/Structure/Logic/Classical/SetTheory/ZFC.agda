open import Functional hiding (Domain)
import      Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.ZFC {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Lang.Instance
import      Lvl
open import Structure.Logic.Classical.NaturalDeduction.Proofs            ⦃ classicLogic ⦄
open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation                 ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Constructive.Functions.Properties            ⦃ constructiveLogicSignature ⦄

private
  module Meta where
    open import Numeral.Finite           public
    open import Numeral.Finite.Bound{ℓₗ} public
    open import Numeral.Natural                public

-- The symbols/signature of ZFC set theory.
record Signature : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  infixl 3000 _∪_
  infixl 3001 _∩_
  infixl 3002 _⨯_ _∖_

  field
    -- Empty set
    -- The set consisting of no elements.
    ∅ : Domain

    -- Pair set.
    -- The set consisting of only two elements.
    pair : Domain → Domain → Domain

    -- Subset filtering.
    -- The subset of the specified set where all elements satisfy the specified formula.
    filter : Domain → (Domain → Formula) → Domain

    -- Power set.
    -- The set of all subsets of the specified set.
    ℘ : Domain → Domain

    -- Union over arbitrary sets.
    -- Constructs a set which consists of elements which are in any of the specified sets.
    ⋃ : Domain → Domain

    -- An inductive set.
    -- A set which has the `Inductive`-property. Also infinite.
    inductiveSet : Domain

    -- The map of a set.
    -- The set of values when a function is applied to every element of a set.
    -- Or: The image of the function on the set.
    -- Or: The image of the function.
    map : (Domain → Domain) → Domain → Domain

    -- An inverse function of a function from its domain to its image.
    inv : (Domain → Domain) → Domain → Domain

  -- Singleton set.
  -- A set consisting of only a single element.
  singleton : Domain → Domain
  singleton(s) = pair(s)(s)

  -- Union operator.
  -- Constructs a set which consists of both elements from LHS and RHS.
  _∪_ : Domain → Domain → Domain
  a ∪ b = ⋃(pair a b)

  -- Intersection operator.
  -- Constructs a set which consists of elements which are in both LHS and RHS.
  _∩_ : Domain → Domain → Domain
  a ∩ b = filter(a)(_∈ b)

  -- "Without"-operator.
  -- Constructs a set which consists of elements which are in LHS, but not RHS.
  _∖_ : Domain → Domain → Domain
  a ∖ b = filter(a)(_∉ b)

  -- Intersection over arbitrary sets.
  -- Constructs a set which consists of elements which are in all of the specified sets.
  ⋂ : Domain → Domain
  ⋂(a) = filter(⋃(a)) (a₁ ↦ ∀ₗ(a₂ ↦ (a₂ ∈ a) ⟶ (a₁ ∈ a₂)))

  -- Tuple value.
  -- An ordered pair of values.
  _,_ : Domain → Domain → Domain
  a , b = pair(singleton(a)) (pair(a)(b))

  -- Set product (Set of tuples) (Cartesian product).
  _⨯_ : Domain → Domain → Domain
  a ⨯ b = filter(℘(℘(a ∪ b))) (t ↦ ∃ₗ(x ↦ (x ∈ a) ∧ ∃ₗ(y ↦ (y ∈ b) ∧ (t ≡ (x , y)))))

  identityPairing : Domain → Domain
  identityPairing(D) = filter(D ⨯ D) (xy ↦ ∃ₗ(a ↦ xy ≡ (a , a)))

  -- swappedPairing : Domain → Domain
  -- swappedPairing() = 

  -- Set product over a finite indexed family (Cartesian product).
  -- TODO: Not really like this. See definition of (_⨯_) and (_,_), and try to express the same here
  -- TODO: Also, make it possible to take the set product of infinite indexed families
  -- TODO: Maybe just use functions like (𝕟(n) →ₛₑₜ _) for finite and (ℕ → _) for infinite
  -- ∏_ : ∀{n} → FiniteIndexedFamily(n) → Domain
  -- ∏_ {Meta.𝟎}            _ = singleton(∅)
  -- ∏_ {Meta.𝐒(Meta.𝟎)}    I = I(Meta.𝟎)
  -- ∏_ {Meta.𝐒(Meta.𝐒(n))} I = I(Meta.maximum) ⨯ (∏_ {Meta.𝐒(n)} (I ∘ Meta.bound-𝐒))

  -- Quotient set.
  -- The set of equivalence classes.
  _/_ : Domain → BinaryRelator → Domain
  a / (_▫_) = filter(℘(a))(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(y ↦ x ▫ y)))

  -- Equivalence class
  -- The set of elements which are equivalent to the specified one.
  [_of_,_] : Domain → Domain → BinaryRelator → Domain
  [ x of a , (_▫_) ] = filter(a)(y ↦ x ▫ y)

  -- TODO: Implement a choice function (the "axiom of choice" one) by inv
  -- choice : Domain → Domain → Domain

  -- The unmap of a set.
  -- The set of elements in the domain X when applied to a function gives an element in Y.
  -- Or: The inverse image of the function on the set.
  -- Or: The pre-image of the function on the set.
  -- Note:
  --   The domain is neccessary because a class function's domain is not neccesarily a set.
  --   For example: `const(x): Domain → Domain` for any (x: Domain) is a class function for which its domain is not a set.
  --   This is because const is defined for all objects in `Domain`, so if a set would have to have all objects in `Domain`, it has to be the universal set, but there is no universal set.
  unmap : Domain → (Domain → Domain) → Domain → Domain
  unmap(X) f(Y) = filter(X) (x ↦ f(x) ∈ Y)

{-
module Function ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄

  record SetRepresentable (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
    constructor intro

    field
      set : Domain

    field
      proof : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (f(x) ≡ y) ⟷ ((x , y) ∈ set))))

  -- An instance of Type(f) means that the function f has a default domain and codomain, and a proof that the function actually are closed inside this domain/codomain pair.
  record Type (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
    constructor intro
    field
      domain   : Domain
      codomain : Domain

    field
      closure : Proof(∀ₛ(domain)(x ↦ f(x) ∈ codomain))
  open Type ⦃ ... ⦄ public
-}

module Tuple ⦃ signature : Signature ⦄ where -- TODO: Move
  open Signature ⦃ ... ⦄

  left : Domain → Domain
  left(s) = ⋃(⋂ s)

  right : Domain → Domain
  right(s) = (⋃ s) ∖ left(s)

-- A model of natural numbers expressed in set theory (using only sets).
module NumeralNatural ⦃ signature : Signature ⦄ where -- TODO: Move
  open Signature ⦃ ... ⦄

  -- The zero constant from the standard inductive set definition of ℕ in ZFC set theory.
  𝟎 : Domain
  𝟎 = ∅

  -- The successor function from the standard inductive set definition of ℕ in ZFC set theory.
  -- This means that all lesser numbers are contained in every number.
  -- Examples:
  -- • 0: {}
  -- • 1: 0∪{0} = {0} = {{},{{}}}
  -- • 2: 1∪{1} = {0}∪{1} = {0,1} = {{},{{},{{}}}}
  -- • 3: 2∪{2} = {0,1}∪{2} = {0,1,2} = {{{},{{},{{}}}},{{{},{{},{{}}}}}}
  -- • 4: 3∪{3} = {0,1,2}∪{3} = {0,1,2,3} = {{{{},{{},{{}}}},{{{},{{},{{}}}}}},{{{{},{{},{{}}}},{{{},{{},{{}}}}}}}}
  𝐒 : Domain → Domain
  𝐒(n) = n ∪ singleton(n)

  -- A set is ℕ-inductive when has zero and all its successors.
  -- In loose terms: Inductive(I) means (I ⊆ ℕ)
  Inductive : Domain → Formula
  Inductive(I) = (𝟎 ∈ I) ∧ (∀ₗ(x ↦ (x ∈ I) ⟶ (𝐒(x) ∈ I)))

  -- The "smallest" inductive set is the set of natural numbers.
  -- All elements which can be expressed using only 𝟎 and 𝐒.
  ℕ : Domain
  ℕ = ⋂(filter(℘(inductiveSet)) Inductive) -- TODO: This pattern seems useful

  -- The relation "lesser than" in this model of ℕ.
  -- This works for all elements in ℕ by the definition of 𝟎 and 𝐒.
  _<_ : BinaryRelator
  a < b = a ∈ b

  _≤_ : BinaryRelator
  a ≤ b = (a < b) ∨ (a ≡ b)

  _>_ : BinaryRelator
  a > b = b < a

  _≥_ : BinaryRelator
  a ≥ b = b ≤ a

  infixl 2000 _<_ _≤_ _>_ _≥_

  𝕟 : Domain → Domain
  𝕟(n) = filter(ℕ) (_< n)

module Axioms ⦃ signature : Signature ⦄ where
  open NumeralNatural using () renaming (Inductive to [ℕ]-Inductive)
  open Signature ⦃ ... ⦄

  -- `∅` is a set which is empty.
  -- • Allows a construction of an empty set.
  EmptySetInclusion : Formula
  EmptySetInclusion = Empty(∅)

  -- `pair` is the construction of a set with two elements.
  -- • Allows a construction of a set with two elements.
  PairingInclusion : Formula
  PairingInclusion = ∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ (∀ₗ(x ↦ (x ∈ pair(x₁)(x₂)) ⟷ (x ≡ x₁)∨(x ≡ x₂)))))

  -- `filter` is the set which is the subset of a set where all elements satisfies a predicate.
  RestrictedComprehension : (Domain → Formula) → Formula
  RestrictedComprehension(φ) = ∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x)))))

  -- `℘` is the construction of a set which contains all the subsets of a set.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSetInclusion : Formula
  PowerSetInclusion = ∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s)))

  -- `⋃` is the construction of a set which contains all the elements of a collection of sets.
  -- • Allows a construction of a set that is the union of some sets.
  UnionInclusion : Formula
  UnionInclusion = ∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s))))

  -- `inductiveSet` is ℕ-inductive.
  -- • An inductive set is infinite, so this implies that an infinite set exists.
  -- • Makes it possible to construct the set of natural numbers (ℕ).
  Infinity : Formula
  Infinity = [ℕ]-Inductive(inductiveSet)

  -- Set identity is extensionally determined. More specifically by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality : Formula
  Extensionality = ∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂)))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Makes every set have an ordinal rank.
  Regularity : Formula
  Regularity = ∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂))))

  -- `map` is the construction of the image of a function restricted to a set.
  -- • The `map`-function on a function is a function from sets to sets.
  Replacement : (Domain → Domain) → Formula
  Replacement(f) = ∀ₗ(A ↦ ∀ₗ(y ↦ (y ∈ map f(A)) ⟷ ∃ₛ(A)(x ↦ y ≡ f(x))))
  -- ReplacementTraditional = ∀{φ : Domain → Domain → Formula} → Proof(∀ₗ(A ↦ TotalFunction(φ)(A) ⟶ ∃ₗ(B ↦ ∀ₗ(y ↦ (y ∈ B) ⟷ ∃ₗ(x ↦ (x ∈ A) ∧ φ(x)(y))))))

  -- The set product of non-empty finite indexed family of sets where all the sets are non-empty is non-empty.
  -- TODO: Should the indexed family really be finite? https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products
  -- Choice = ∀{n : Meta.ℕ}{F : FiniteIndexedFamily(Meta.𝐒(n))} → (∀{i : Meta.𝕟(Meta.𝐒(n))} → Proof(NonEmpty(F(i)))) → Proof(NonEmpty(∏ F))

  -- `inv` constructs the right inverse for function composition.
  -- • All surjective class functions have a right inverse.
  -- • An element applied to the inverse function of a function yields/returns one of the arguments that yield/return this element as a value when it exists.
  -- TODO: MAybe this is too strong of a statement? Because the image is not neccessarily a set if the class function is defined for all objects (in the domain) in the theory? Is this really equivalent to `ChoiceTraditional`?
  Choice : (Domain → Domain) → Formula
  Choice(f) = ∀ₗ(y ↦ (Value f(y)) ⟶ ((f ∘ (inv f))(y) ≡ y))

  -- ChoiceTraditional = Proof(∀ₗ(s ↦ (∅ ∉ s) ⟶ ∃ₛ(s →ₛₑₜ (⋃ s))(f ↦ ∀ₛ(s)(x ↦ ∀ₛ(⋃ s)(y ↦ ((x , y) ∈ f) ⟶ (y ∈ x))))))
  -- ChoiceTraditional : (Domain → Domain → Domain) → Formula
  -- ChoiceTraditional(choice) = ∀ₗ(s ↦ ∀ₛ(s)(x ↦ NonEmpty(x) ⟶ (choice(s)(x) ∈ x)))

record Z ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)

record ZF ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)
    regular       : Proof(Regularity)
    replacement   : ∀{f} → Proof(Replacement(f))

record ZFC ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ ℓₘₗ) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Proof(Extensionality)
    empty         : Proof(EmptySetInclusion)
    pairing       : Proof(PairingInclusion)
    comprehension : ∀{φ} → Proof(RestrictedComprehension(φ))
    union         : Proof(UnionInclusion)
    power         : Proof(PowerSetInclusion)
    infinity      : Proof(Infinity)
    regular       : Proof(Regularity)
    replacement   : ∀{f} → Proof(Replacement(f))
    choice        : ∀{f} → Proof(Choice(f))
