open import Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory.ZFC {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Formula) where

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open        Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} (Proof) renaming (Theory to PredicateEqTheory)
open import Structure.Logic.Classical.NaturalDeduction.Proofs {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Formula} {Domain} {Proof} ⦃ predicateEqTheory ⦄
open import Structure.Logic.Classical.SetTheory.BoundedQuantification ⦃ predicateEqTheory ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation ⦃ predicateEqTheory ⦄ (_∈_)

open PredicateEqTheory (predicateEqTheory)
private
  module Meta where
    open import Numeral.FiniteStrict           public
    open import Numeral.FiniteStrict.Bound{ℓₗ} public
    open import Numeral.Natural                public

-- The type of a meta-function. Functions on the domain in the meta-logic.
Function : Set(_)
Function = (Domain → Domain)

FiniteIndexedFamily : Meta.ℕ → Set(_)
FiniteIndexedFamily(n) = Meta.𝕟(n) → Domain

InfiniteIndexedFamily : Set(_)
InfiniteIndexedFamily = Meta.ℕ → Domain

-- The symbols/signature of ZFC set theory.
record Signature : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
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

  -- Set product over a finite indexed family (Cartesian product).
  -- TODO: Not really like this. See definition of (_⨯_) and (_,_), and try to express the same here
  -- TODO: Also, make it possible to take the set product of infinite indexed families
  ∏_ : ∀{n} → FiniteIndexedFamily(n) → Domain
  ∏_ {Meta.𝟎}            _ = singleton(∅)
  ∏_ {Meta.𝐒(Meta.𝟎)}    I = I(Meta.𝟎)
  ∏_ {Meta.𝐒(Meta.𝐒(n))} I = I(Meta.maximum) ⨯ (∏_ {Meta.𝐒(n)} (I ∘ Meta.bound-𝐒))

  -- Quotient set.
  -- The set of equivalence classes.
  _/_ : Domain → BinaryRelator → Domain
  a / (_▫_) = filter(℘(a))(aₛ ↦ ∀ₛ(aₛ)(x ↦ ∀ₛ(aₛ)(y ↦ x ▫ y)))

  -- Equivalence class
  -- The set of elements which are equivalent to the specified one.
  [_of_,_] : Domain → Domain → BinaryRelator → Domain
  [ x of a , (_▫_) ] = filter(a)(y ↦ x ▫ y)

module Function ⦃ signature : Signature ⦄ where
  open Signature ⦃ ... ⦄

  record SetRepresentable (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
    constructor intro

    field
      set : Domain

    field
      proof : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (f(x) ≡ y) ⟷ ((x , y) ∈ set))))

  -- An instance of Type(f) means that the function f has a default domain and codomain, and a proof that the function actually are closed inside this domain/codomain pair.
  record Type (f : Function) : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
    constructor intro
    field
      domain   : Domain
      codomain : Domain

    field
      closure : Proof(∀ₛ(domain)(x ↦ f(x) ∈ codomain))

    -- The image of the function f on the set a.
    -- Applies this function on every element in the set a, yielding a new set.
    map : Domain → Domain
    map a = filter(codomain)(y ↦ ∃ₛ(a)(x ↦ y ≡ f(x)))

    -- The image of the function.
    -- The set of all elements that the function can yield/points to.
    ⊶ : Domain
    ⊶ = map(domain)
  open Type ⦃ ... ⦄ public

  PartialFunctionSet : Domain → Domain → Formula
  PartialFunctionSet(D)(s) = ∀ₛ(D)(x ↦ Unique(y ↦ (x , y) ∈ s))

  -- The statement that the set s can be interpreted as a function with a specified domain.
  -- The following describes the relation in an inexact notation:
  -- • ∀(x∊A)∀y. ((x,y) ∈ S) ⇔ (S(x) = y)
  FunctionSet : Domain → Domain → Formula
  FunctionSet(D)(s) = ∀ₛ(D)(x ↦ ∃ₗ!(y ↦ (x , y) ∈ s))

  -- The set of function sets, all sets which can be interpreted as a function.
  _^_ : Domain → Domain → Domain
  B ^ A = filter(℘(A ⨯ B)) (FunctionSet(A))

  _→ₛₑₜ_ = swap _^_

module Structure where
  -- Structures in meta-functions.
  module Function' where -- TODO: Temporary naming fix with tick
    module Properties ⦃ signature : Signature ⦄ where
      open Function renaming (Type to Metatype)

      Type : Function → Domain → Domain → Formula
      Type(f)(X)(Y) = ∀ₛ(X)(x ↦ f(x) ∈ Y)

      Closed : Domain → Function → Formula
      Closed(S)(f) = Type(f)(S)(S)

      Injective : (f : Function) → ⦃ _ : Metatype(f) ⦄ → Formula
      Injective(f) = ∀ₛ(domain{f})(x ↦ ∀ₛ(domain{f})(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

      Surjective : (f : Function) → ⦃ _ : Metatype(f) ⦄ → Formula
      Surjective(f) = ∀ₛ(codomain{f})(y ↦ ∃ₛ(domain{f})(x ↦ f(x) ≡ y))

      Bijective : (f : Function) → ⦃ _ : Metatype(f) ⦄ → Formula
      Bijective(f) = Injective(f) ∧ Surjective(f)

  module Relator where
    module Properties where
      Reflexivity : Domain → BinaryRelator → Formula
      Reflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ x ▫ x)

      Irreflexivity : Domain → BinaryRelator → Formula
      Irreflexivity(S)(_▫_) = ∀ₛ(S)(x ↦ ¬(x ▫ x))

      Symmetry : Domain → BinaryRelator → Formula
      Symmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ (y ▫ x)))

      Asymmetry : Domain → BinaryRelator → Formula
      Asymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ⟶ ¬(y ▫ x)))

      Antisymmetry : Domain → BinaryRelator → Formula
      Antisymmetry(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y)∧(y ▫ x) ⟶ (x ≡ y)))

      Transitivity : Domain → BinaryRelator → Formula
      Transitivity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ (x ▫ y)∧(y ▫ z) ⟶ (x ▫ z))))

      Equivalence : Domain → BinaryRelator → Formula
      Equivalence(S)(_▫_) = Reflexivity(S)(_▫_) ∧ Symmetry(S)(_▫_) ∧ Transitivity(S)(_▫_)

      SymmetricallyTotal : Domain → BinaryRelator → Formula
      SymmetricallyTotal(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ∨ (y ▫ x)))

  module Ordering where
    open Relator.Properties

    Minima : Domain → BinaryRelator → Domain → Formula
    Minima(S)(_≤_)(min) = ∀ₛ(S)(x ↦ min ≤ x)

    Maxima : Domain → BinaryRelator → Domain → Formula
    Maxima(S)(_≤_)(max) = ∀ₛ(S)(x ↦ x ≤ max)

    module _  ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      lowerBounds : Domain → BinaryRelator → Domain → Domain
      lowerBounds(S)(_≤_)(Sₛ) = filter(S)(Minima(S)(_≤_))

      upperBounds : Domain → BinaryRelator → Domain → Domain
      upperBounds(S)(_≤_)(Sₛ) = filter(S)(Maxima(S)(_≤_))

      interval : Domain → BinaryRelator → Domain → Domain → Domain
      interval(S)(_≤_) (a)(b) = filter(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Bounded : Domain → BinaryRelator → Domain → Domain → Formula
      Bounded(S)(_≤_) (a)(b) = ∀ₛ(S)(s ↦ (a ≤ s) ∧ (s ≤ b))

      Infima : Domain → BinaryRelator → Domain → Domain → Formula
      Infima(S)(_≤_)(Sₛ)(inf) = Maxima(lowerBounds(S)(_≤_)(Sₛ))(_≤_)(inf)

      Suprema : Domain → BinaryRelator → Domain → Domain → Formula
      Suprema(S)(_≤_)(Sₛ)(sup) = Minima(upperBounds(S)(_≤_)(Sₛ))(_≤_)(sup)

    module Weak where
      PartialOrder : Domain → BinaryRelator → Formula
      PartialOrder(S)(_≤_) = Reflexivity(S)(_≤_) ∧ Antisymmetry(S)(_≤_) ∧ Transitivity(S)(_≤_)

      TotalOrder : Domain → BinaryRelator → Formula
      TotalOrder(S)(_≤_) = PartialOrder(S)(_≤_) ∧ SymmetricallyTotal(S)(_≤_)

    module Strict where
      Order : Domain → BinaryRelator → Formula
      Order(S)(_<_) = Irreflexivity(S)(_<_) ∧ Asymmetry(S)(_<_) ∧ Transitivity(S)(_<_)

      Dense : Domain → BinaryRelator → Formula
      Dense(S)(_<_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x < y) ⟶ ∃ₛ(S)(z ↦ (x < z)∧(z < y))))

  module Operator where
    BinaryOperator : Set(_)
    BinaryOperator = (Domain → Domain → Domain)

    module Properties where
      AssociativityPattern : Domain → Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
      AssociativityPattern(x)(y)(z)(_▫₁_)(_▫₂_)(_▫₃_)(_▫₄_) = (((x ▫₁ y) ▫₂ z) ≡ (x ▫₃ (y ▫₄ z)))

      Type : BinaryOperator → Domain → Domain → Domain → Formula
      Type(_▫_)(X)(Y)(Z) = ∀ₛ(X)(x ↦ ∀ₛ(Y)(y ↦ (x ▫ y) ∈ Z))

      Closed : Domain → BinaryOperator → Formula
      Closed(S)(_▫_) = Type(_▫_)(S)(S)(S)

      Commutativity : Domain → BinaryOperator → Formula
      Commutativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ (x ▫ y) ≡ (y ▫ x)))

      Associativity : Domain → BinaryOperator → Formula
      Associativity(S)(_▫_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ AssociativityPattern(x)(y)(z)(_▫_)(_▫_)(_▫_)(_▫_))))

      Identityₗ : Domain → BinaryOperator → Domain → Formula
      Identityₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (id ▫ x) ≡ x)

      Identityᵣ : Domain → BinaryOperator → Domain → Formula
      Identityᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ (x ▫ id) ≡ x)

      Identity : Domain → BinaryOperator → Domain → Formula
      Identity(S)(_▫_)(id) = Identityₗ(S)(_▫_)(id) ∧ Identityᵣ(S)(_▫_)(id)

      Invertibleₗ : Domain → BinaryOperator → Domain → Formula
      Invertibleₗ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x⁻¹ ▫ x) ≡ id))

      Invertibleᵣ : Domain → BinaryOperator → Domain → Formula
      Invertibleᵣ(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ (x ▫ x⁻¹) ≡ id))

      Invertible : Domain → BinaryOperator → Domain → Formula
      Invertible(S)(_▫_)(id) = ∀ₛ(S)(x ↦ ∃ₛ(S)(x⁻¹ ↦ ((x⁻¹ ▫ x) ≡ id) ∧ ((x ▫ x⁻¹) ≡ id)))

      Distributivityₗ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityₗ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ (x ▫₁ (y ▫₂ z)) ≡ ((x ▫₁ y) ▫₂ (x ▫₁ z)))))

      Distributivityᵣ : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivityᵣ(S)(_▫₁_)(_▫₂_) = ∀ₛ(S)(x ↦ ∀ₛ(S)(y ↦ ∀ₛ(S)(z ↦ ((x ▫₂ y) ▫₁ z) ≡ ((x ▫₁ z) ▫₂ (y ▫₁ z)))))

      Distributivity : Domain → BinaryOperator → BinaryOperator → Formula
      Distributivity(S)(_▫₁_)(_▫₂_) = Distributivityₗ(S)(_▫₁_)(_▫₂_) ∧ Distributivityᵣ(S)(_▫₁_)(_▫₂_)

      Compatibility : Domain → Domain → BinaryOperator → BinaryOperator → Formula
      Compatibility(A)(B)(_▫₁_)(_▫₂_) = ∀ₛ(A)(a₁ ↦ ∀ₛ(A)(a₂ ↦ ∀ₛ(B)(b ↦ AssociativityPattern(a₁)(a₂)(b)(_▫₁_)(_▫₁_)(_▫₂_)(_▫₁_))))

      Semigroup : Domain → BinaryOperator → Formula
      Semigroup(S)(_▫_) = Closed(S)(_▫_) ∧ Associativity(S)(_▫_)

      Monoid : Domain → BinaryOperator → Formula
      Monoid(S)(_▫_) = Semigroup(S)(_▫_) ∧ ∃ₛ(S)(Identity(S)(_▫_))

      Group : Domain → BinaryOperator → Formula
      Group(S)(_▫_) = Monoid(S)(_▫_) ∧ ∀ₛ(S)(id ↦ Identity(S)(_▫_)(id) ⟶ Invertible(S)(_▫_)(id))

      CommutativeGroup : Domain → BinaryOperator → Formula
      CommutativeGroup(S)(_▫_) = Group(S)(_▫_) ∧ Commutativity(S)(_▫_)

      Rng : Domain → BinaryOperator → BinaryOperator → Formula
      Rng(S)(_▫₁_)(_▫₂_) = CommutativeGroup(S)(_▫₁_) ∧ Semigroup(S)(_▫₂_) ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      Ring : Domain → BinaryOperator → BinaryOperator → Formula
      Ring(S)(_▫₁_)(_▫₂_) = CommutativeGroup(S)(_▫₁_) ∧ Monoid(S)(_▫₂_) ∧ Distributivity(S)(_▫₂_)(_▫₁_)

      module _  ⦃ signature : Signature ⦄ where
        open Signature ⦃ ... ⦄

        Field : Domain → BinaryOperator → BinaryOperator → Formula
        Field(S)(_▫₁_)(_▫₂_) = CommutativeGroup(S)(_▫₁_) ∧ ∀ₛ(S)(id₁ ↦ Identity(S)(_▫₁_)(id₁) ⟶ CommutativeGroup(S ∖ singleton(id₁))(_▫₂_)) ∧ Distributivity(S)(_▫₂_)(_▫₁_)

        -- TODO: Not finished
        VectorSpace : Domain → Domain → BinaryOperator → BinaryOperator → BinaryOperator → BinaryOperator → Formula
        VectorSpace(V)(S)(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) = CommutativeGroup(V)(_+ᵥ_) ∧ Field(S)(_+ₛ_)(_⋅ₛ_) ∧ ∀ₛ(S)(id ↦ Identity(S)(_⋅ₛ_)(id) ⟶ Identityₗ(V)(_⋅ₛᵥ_)(id)) ∧ Compatibility(S)(V)(_⋅ₛᵥ_)(_⋅ₛ_) -- ∧ Distributivityₗ() ∧ Distributivityᵣ()

  module Numeral where
    module Natural ⦃ signature : Signature ⦄ where
      open Signature ⦃ ... ⦄

      Induction : Domain → Domain → (Domain → Domain) → (Domain → Formula) → Formula
      Induction(ℕ)(𝟎)(𝐒) (φ) = (φ(𝟎) ∧ ∀ₛ(ℕ)(n ↦ φ(n) ⟶ φ(𝐒(n)))) ⟶ ∀ₛ(ℕ)(φ)

      -- Peano : Domain → Domain → (Domain → Domain) → Formula
      -- Peano(ℕ)(𝟎)(𝐒) = (𝟎 ∈ ℕ) ∧ Function'.Properties.Closed(ℕ)(𝐒) ∧ Function'.Properties.Injective(ℕ)(𝐒) ∧ ∀ₛ(S)(n ↦ 𝐒(n) ≢ 𝟎) ∧ Induction(ℕ)(𝟎)(𝐒)

-- A model of natural numbers expressed in set theory (using only sets).
module NumeralNatural ⦃ signature : Signature ⦄ where
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

  -- _+_ : Domain → Domain → Domain
  -- a + b = 

  infixl 2000 _<_ _≤_ _>_ _≥_

-- A model of integers expressed in set theory (using only sets).
module NumeralInteger ⦃ signature : Signature ⦄ where
  open NumeralNatural

  -- a

module Axioms ⦃ signature : Signature ⦄ where
  open NumeralNatural using () renaming (Inductive to [ℕ]-Inductive)
  open Signature ⦃ ... ⦄

  -- A set which is empty exists.
  -- • Allows a construction of the empty set.
  EmptySet = Proof(Empty(∅))

  -- A set with two elements exists.
  -- • Allows a construction of a set with two elements.
  Pairing = Proof(∀ₗ(x₁ ↦ ∀ₗ(x₂ ↦ (∀ₗ(x ↦ (x ∈ pair(x₁)(x₂)) ⟷ (x ≡ x₁)∨(x ≡ x₂))))))

  -- A set which is the subset of a set where all elements satisfies a predicate exists.
  RestrictedComprehension = ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))

  -- A set which contains all the subsets of a set exists.
  -- • Allows a construction of a set that is the powerset of a set.
  PowerSet = Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))

  -- A set which contains all the elements of a group of sets exists.
  -- • Allows a construction of a set that is the union of some sets.
  Union = Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))

  -- An infinite set (specifically, a ℕ-inductive set (which just happens to be infinite)) exists.
  Infinity = Proof([ℕ]-Inductive(inductiveSet))

  -- Set equality is determined by its contents.
  -- • Guarantees the definition of equality for sets.
  Extensionality = Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁)⟷(x ∈ s₂)) ⟷ (s₁ ≡ s₂))))

  -- A non-empty set contain sets that are disjoint to it.
  -- • Prevents sets containing themselves.
  -- • Making every set have an ordinal rank.
  Regularity = Proof(∀ₗ(s₁ ↦ (NonEmpty(s₁) ⟶ ∃ₗ(s₂ ↦ (s₂ ∈ s₁) ∧ Disjoint(s₁)(s₂)))))

  Replacement = ∀{φ : Domain → Domain → Formula} → Proof(∀ₗ(A ↦ TotalFunction(φ)(A) ⟶ ∃ₗ(B ↦ ∀ₗ(y ↦ (y ∈ B) ⟷ ∃ₗ(x ↦ (x ∈ A) ∧ φ(x)(y))))))

  -- The set product of non-empty finite indexed family of sets where all the sets are non-empty is non-empty.
  -- TODO: Should the indexed family really be finite? https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products
  Choice = ∀{n : Meta.ℕ}{F : FiniteIndexedFamily(Meta.𝐒(n))} → (∀{i : Meta.𝕟(Meta.𝐒(n))} → Proof(NonEmpty(F(i)))) → Proof(NonEmpty(∏ F))
  -- ∀{s} → Proof(∅ ∉ s) → ∃(s → (⋃ s))(f ↦ ) Proof(∀ₛ(s)(x ↦ f(x) ∈ x))

record ZF ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Extensionality
    empty         : EmptySet
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet

record ZFC ⦃ signature : Signature ⦄ : Set((ℓₗ Lvl.⊔ ℓₒ) Lvl.⊔ (ℓₘₗ Lvl.⊔ ℓₘₒ)) where
  open Axioms
  open Signature ⦃ ... ⦄

  field
    extensional   : Extensionality
    empty         : EmptySet
    regular       : Regularity
    comprehension : RestrictedComprehension
    pairing       : Pairing
    union         : Union
    replacement   : Replacement
    infinity      : Infinity
    power         : PowerSet
    choice        : Choice

module Proofs ⦃ signature : Signature ⦄ ⦃ axioms : ZF ⦄ where
  open Axioms
  open Signature ⦃ ... ⦄
  open ZF ⦃ ... ⦄

  -- All sets are either empty or non-empty.
  postulate Empty-excluded-middle : ∀{s} → Proof(Empty(s) ∨ NonEmpty(s))

  -- postulate any : ∀{l}{a : Set(l)} → a

  -- All sets that are defined using an equivalence of contained elements are unique
  unique-definition : ∀{φ : Domain → Formula} → Proof(Unique(S ↦ ∀ₗ(x ↦ (x ∈ S) ⟷ φ(x))))
  unique-definition{_} =
    ([∀]-intro(\{S₁} →
      ([∀]-intro(\{S₂} →
        ([→]-intro(proof ↦
          ([↔]-elimᵣ
            ([∀]-elim([∀]-elim extensional{S₁}){S₂})
            ([∀]-intro(\{x} →
              ([↔].transitivity
                ([∀]-elim([∧]-elimₗ(proof)){x})
                ([↔].commutativity([∀]-elim([∧]-elimᵣ(proof)){x}))
              )
            ))
          )
        ))
      ))
    ))

  postulate [≡]-from-subset : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ ((x ⊇ y) ∧ (x ⊆ y)) ⟷ (x ≡ y))))

  [∅]-containment : Proof(∀ₗ(x ↦ (x ∈ ∅) ⟷ ⊥))
  [∅]-containment =
    ([∀]-intro (\{x} →
      ([↔]-intro
        ([⊥]-elim)
        ([⊥]-intro
          ([∀]-elim empty{x})
        )
      )
    ))

  [∅]-subset : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [∅]-subset =
    ([∀]-intro(\{s} →
      ([∀]-intro(\{x} →
        ([→]-intro(xin∅ ↦
          [⊥]-elim ([↔]-elimᵣ([∀]-elim [∅]-containment {x}) (xin∅))
        ))
      ))
    ))

  postulate [∅]-subset-is-equal : Proof(∀ₗ(s ↦ (s ⊆ ∅) ⟶ (s ≡ ∅)))
  -- [∅]-subset-is-equal =
  --   ([∀]-intro(\{s} →
  --     ([→]-intro(s⊆∅ ↦
  --       
  --     ))
  --   ))

  [∃ₛ]-of-[∅] : ∀{P : Domain → Formula} → Proof(¬(∃ₛ ∅ P))
  [∃ₛ]-of-[∅] =
    ([¬]-intro(ep ↦
      [∃ₛ]-elim(\{x} → x∈∅ ↦ _ ↦ [⊥]-elim([⊥]-intro ([∀]-elim empty) x∈∅)) ep
    ))

  postulate [⊆]-minimum : Proof(∀ₗ(min ↦ ∀ₗ(s ↦ min ⊆ s) ⟷ (min ≡ ∅)))

  [⊆]-minima : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [⊆]-minima = [∅]-subset

  [⊆]-reflexivity : Proof(∀ₗ(s ↦ s ⊆ s))
  [⊆]-reflexivity = [∀]-intro(\{_} → [∀]-intro(\{_} → [→].reflexivity))

  [⊆]-antisymmetry : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a)∧(a ⊆ b) ⟶ (a ≡ b))))
  [⊆]-antisymmetry =
    ([∀]-intro(\{a} →
      ([∀]-intro(\{b} →
        ([→]-intro(abba ↦
          ([↔]-elimᵣ([∀]-elim([∀]-elim extensional{a}){b}))
          ([∀]-intro(\{x} →
            ([↔]-intro
              ([→]-elim([∀]-elim([∧]-elimₗ abba){x}))
              ([→]-elim([∀]-elim([∧]-elimᵣ abba){x}))
            )
          ))
        ))
      ))
    ))

  [⊆]-transitivity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ⊆ b)∧(b ⊆ c) ⟶ (a ⊆ c)))))
  [⊆]-transitivity =
    ([∀]-intro(\{a} →
      ([∀]-intro(\{b} →
        ([∀]-intro(\{c} →
          ([→]-intro(abbc ↦
            ([∀]-intro(\{x} →
              ([→].transitivity
                ([∀]-elim([∧]-elimₗ abbc){x})
                ([∀]-elim([∧]-elimᵣ abbc){x})
              )
            ))
          ))
        ))
      ))
    ))

  pair-containment : Proof(∀ₗ(a₁ ↦ ∀ₗ(a₂ ↦ (∀ₗ(x ↦ (x ∈ pair(a₁)(a₂)) ⟷ (x ≡ a₁)∨(x ≡ a₂))))))
  pair-containment = pairing

  filter-containment : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))
  filter-containment = comprehension

  filter-subset : ∀{φ} → Proof(∀ₗ(s ↦ filter(s)(φ) ⊆ s))
  filter-subset =
    ([∀]-intro(\{s} →
      ([∀]-intro(\{x} →
        ([→]-intro(xinfilter ↦
          [∧]-elimₗ([↔]-elimᵣ([∀]-elim([∀]-elim filter-containment{s}){x}) (xinfilter))
        ))
      ))
    ))

  filter-of-[∅] : ∀{φ} → Proof(filter(∅)(φ) ≡ ∅)
  filter-of-[∅] =
    ([→]-elim
      ([∀]-elim([∀]-elim [⊆]-antisymmetry))
      ([∧]-intro
        ([∀]-elim [∅]-subset)
        ([∀]-elim filter-subset)
      )
    )

  filter-property : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₛ(filter(s)(φ)) φ))
  filter-property =
    ([∀]-intro(\{s} →
      ([∀]-intro(\{x} →
        ([→]-intro(xinfilter ↦
          [∧]-elimᵣ([↔]-elimᵣ([∀]-elim([∀]-elim filter-containment{s}){x}) (xinfilter))
        ))
      ))
    ))

  [℘]-containment : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))
  [℘]-containment = power

  postulate [℘]-of-[∅] : Proof(℘(∅) ≡ singleton(∅))
  postulate [℘]-contains-empty : Proof(∀ₗ(s ↦ ∅ ∈ ℘(s)))
  postulate [℘]-contains-self  : Proof(∀ₗ(s ↦ s ∈ ℘(s)))

  [⋃]-containment : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₛ(ss)(s ↦ x ∈ s))))
  [⋃]-containment = union

  postulate [⋃]-containing-max : Proof(∀ₗ(s ↦ ∀ₛ(s)(max ↦ ∀ₛ(s)(x ↦ x ⊆ max) ⟶ (⋃(s) ≡ max))))
  postulate [⋃]-subset : Proof(∀ₗ(s ↦ ∀ₛ(s)(x ↦ x ⊆ ⋃(s))))

  postulate [⋃]-of-[∅] : Proof(⋃(∅) ≡ ∅)
  -- [⋃]-of-empty =
  --   ([⋃]-containment
  --   )
  --   [∃ₛ]-of-[∅]

  singleton-containment : Proof(∀ₗ(a ↦ ∀ₗ(x ↦ (x ∈ singleton(a)) ⟷ (x ≡ a))))
  singleton-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{x} →
        [↔].transitivity
          ([∀]-elim([∀]-elim([∀]-elim(pair-containment){a}){a}){x})
          ([↔]-intro ([∨].redundancyₗ) ([∨].redundancyᵣ))
      ))
    ))

  postulate singleton-contains-self : Proof(∀ₗ(s ↦ s ∈ singleton(s)))

  [∪]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∪ b)) ⟷ (x ∈ a)∨(x ∈ b)))))
  [∪]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-intro (\{x} →
          ([∀]-elim([∀]-elim [⋃]-containment{pair(a)(b)}){x})
          〔ₗ [↔].transitivity 〕
          ([↔]-with-[∃] (\{s} →
            ([↔]-with-[∧]ₗ ([∀]-elim([∀]-elim([∀]-elim pair-containment{a}){b}){s}))
            〔ₗ [↔].transitivity 〕
            ([∧][∨]-distributivityᵣ)
            〔ₗ [↔].transitivity 〕
            [↔]-with-[∨] ([≡]-substitute-this-is-almost-trivial) ([≡]-substitute-this-is-almost-trivial)
          ))
          〔ₗ [↔].transitivity 〕
          ([↔]-intro ([∃].redundancyₗ) ([∃].redundancyᵣ))
        ))
      ))
    ))

  postulate [∪]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∪ b ≡ b ∪ a)))
  postulate [∪]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∪ b) ∪ c ≡ a ∪ (b ∪ c)))))
  postulate [∪]-identityₗ : Proof(∀ₗ(s ↦ ∅ ∪ s ≡ s))
  postulate [∪]-identityᵣ : Proof(∀ₗ(s ↦ s ∪ ∅ ≡ s))
  postulate [∪]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ⊆ a ∪ b)))
  postulate [∪]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ b ⊆ a ∪ b)))
  postulate [∪]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∪ b ≡ a)))))
  postulate [∪]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∪ b ≡ b)))))
  postulate [∪]-of-self : Proof(∀ₗ(s ↦ s ∪ s ≡ s))

  [∩]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∩ b)) ⟷ (x ∈ a)∧(x ∈ b)))))
  [∩]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-elim(filter-containment){a})
      ))
    ))

  postulate [∩]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ≡ b ∩ a)))
  postulate [∩]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∩ b) ∩ c ≡ a ∩ (b ∩ c)))))
  postulate [∩]-annihilatorₗ : Proof(∀ₗ(s ↦ ∅ ∩ s ≡ ∅))
  postulate [∩]-annihilatorᵣ : Proof(∀ₗ(s ↦ s ∩ ∅ ≡ s))
  postulate [∩]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ a)))
  postulate [∩]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ b)))
  postulate [∩]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∩ b ≡ b))))
  postulate [∩]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∩ b ≡ a))))
  postulate [∩]-of-self : Proof(∀ₗ(s ↦ s ∩ s ≡ s))

  [∖]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∖ b)) ⟷ (x ∈ a)∧(x ∉ b)))))
  [∖]-containment =
    ([∀]-intro (\{a} →
      ([∀]-intro (\{b} →
        ([∀]-elim(filter-containment){a})
      ))
    ))

  [⋂]-containment : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋂(ss)) ⟷ ∀ₛ(ss)(s ↦ x ∈ s))))
  [⋂]-containment =
    ([∀]-intro (\{ss} →
      ([∀]-intro (\{x} →
        ([↔]-intro
          -- (⟵)-case
          (allssinssxins ↦
            ([↔]-elimₗ
              ([∀]-elim([∀]-elim filter-containment{⋃(ss)}){x})
              ([∧]-intro
                -- x ∈ ⋃(ss)
                ([∨]-elim
                  -- Empty(ss) ⇒ _
                  (allyyninss ↦
                    proof -- TODO: But: Empty(ss) ⇒ (ss ≡ ∅) ⇒ ⋃(ss) ≡ ∅ ⇒ (x ∉ ⋃(ss)) ? Maybe use this argument further up instead to prove something like: (⋂(ss) ≡ ∅) ⇒ (x ∉ ∅)
                  )

                  -- NonEmpty(ss) ⇒ _
                  (existsyinss ↦
                    ([∃]-elim
                      (\{y} → yinss ↦ (
                        ([↔]-elimₗ([∀]-elim([∀]-elim([⋃]-containment){ss}){x}))
                        ([∃]-intro{_}
                          {y}
                          ([∧]-intro
                            -- y ∈ ss
                            (yinss)

                            -- x ∈ y
                            ([→]-elim
                              ([∀]-elim(allssinssxins){y})
                              (yinss)
                            )
                          )
                        )
                      ))
                      (existsyinss)
                    )
                  )
                  (Empty-excluded-middle{ss})
                )

                -- ∀(s∊ss). x∈s
                (allssinssxins)
              )
            )
          )

          -- (⟶)-case
          (xinintersectss ↦
            ([∀]-intro (\{s} →
              ([→]-intro (sinss ↦
                ([→]-elim
                  ([∀]-elim
                    ([∧]-elimᵣ
                      ([↔]-elimᵣ
                        ([∀]-elim
                          ([∀]-elim
                            filter-containment
                            {⋃(ss)}
                          )
                          {x}
                        )
                        (xinintersectss)
                      )
                    )
                    {s}
                  )
                  (sinss)
                )
              ))
            ))
          )
        )
      ))
    ))
    where postulate proof : ∀{a} → a

  postulate [⋂]-containing-min : Proof(∀ₗ(s ↦ ∀ₛ(s)(min ↦ ∀ₛ(s)(x ↦ min ⊆ x) ⟶ (⋂(s) ≡ min))))
  postulate [⋂]-containing-[∅] : Proof(∀ₗ(s ↦ (∅ ∈ s) ⟶ (⋂(s) ≡ ∅)))
  postulate [⋂]-containing-disjoint : Proof(∀ₗ(s ↦ ∃ₛ(s)(a ↦ ∃ₛ(s)(b ↦ Disjoint(a)(b))) ⟶ (⋂(s) ≡ ∅)))
  postulate [⋂]-subset : Proof(∀ₗ(s ↦ ∀ₛ(s)(x ↦ ⋂(s) ⊆ x)))

  -- TODO: Just used for reference. Remove these lines later
  -- ⋂(a) = filter(⋃(ss)) (x ↦ ∀ₗ(a₂ ↦ (a₂ ∈ ss) ⟶ (x ∈ a₂)))
  -- filter-containment : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))
  -- [⋃]-containment : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))


  -- [⨯]-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ⨯ b)) ⟷ ∃ₛ(a)(x₁ ↦ ∃ₛ(b)(x₂ ↦ x ≡ (x₁ , x₂)))))))
  -- [⨯]-containment =

  -- [⋃][℘]-inverse : Proof(∀ₗ(s ↦ ⋃(℘(s)) ≡ s))

  module Quotient {T : Domain} {_≅_ : BinaryRelator} ⦃ equivalence : Proof(Structure.Relator.Properties.Equivalence(T)(_≅_)) ⦄ where
    open Structure.Relator.Properties

    postulate [/]-containment : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
    postulate [/]-pairwise-disjoint : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
    postulate [/]-not-containing-[∅] : Proof(∀ₗ(x ↦ ∅ ∉ (T / (_≅_))))
    postulate [/]-cover : Proof(⋃(T / (_≅_)) ≡ T)
    postulate eqClass-containment : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ∈ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
    postulate eqClass-containing-self : Proof(∀ₗ(a ↦ a ∈ [ a of T , (_≅_) ]))
    postulate eqClass-nonempty : Proof(∀ₗ(a ↦ NonEmpty([ a of T , (_≅_) ])))
    postulate eqClass-equal-disjoint : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ ¬ Disjoint([ a of T , (_≅_) ])([ b of T , (_≅_) ]))))
    postulate eqClass-equal-equivalent : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
    postulate eqClass-equal-containingₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (b ∈ [ a of T , (_≅_) ]))))
    postulate eqClass-equal-containingᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ∈ [ b of T , (_≅_) ]))))

  module FunctionProofs where
    open Function ⦃ signature ⦄

    [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] : ∀{D : Domain}{P : BinaryRelator} → Proof(∀ₗ(x ↦ ∃ₗ(y ↦ (x ∈ D) ⟶ P(x)(y))) ⟷ ∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
    [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] {D}{P} = [↔]-with-[∀] ([∃]-unrelatedᵣ-[→])

    [∀ₛ∃!]-to[∀ₛ∃] : ∀{P : BinaryRelator}{D : Domain} → Proof(∀ₛ(D)(x ↦ ∃ₗ!(y ↦ P(x)(y)))) → Proof(∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
    [∀ₛ∃!]-to[∀ₛ∃] proof =
      ([∀ₛ]-intro(\{x} → xinD ↦
        [∧]-elimₗ([∀ₛ]-elim proof {x} xinD)
      ))

    -- The construction of a meta-function in the meta-logic from a function in the set theory
    fnset-witness : ∀{D} → (f : Domain) → ⦃ _ : Proof(FunctionSet(D)(f)) ⦄ → Function
    fnset-witness f ⦃ proof ⦄ = [∃]-fn-witness ⦃ [↔]-elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] ([∀ₛ∃!]-to[∀ₛ∃] proof) ⦄

    fnset-value : ∀{D} → (f : Domain) → ⦃ proof : Proof(FunctionSet(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ (x , fnset-witness f(x)) ∈ f))
    fnset-value{D} f ⦃ proof ⦄ = [∃]-fn-proof ⦃ [↔]-elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] ([∀ₛ∃!]-to[∀ₛ∃] proof) ⦄

    fnset-proof : ∀{D} → (f : Domain) → ⦃ proof : Proof(FunctionSet(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ ∀ₗ(y ↦ (fnset-witness{D} f ⦃ proof ⦄ x ≡ y) ⟷ ((x , y) ∈ f))))
    fnset-proof{D} f ⦃ proof ⦄ =
      ([∀ₛ]-intro(\{x} → x∈D ↦
        ([∀]-intro(\{y} →
          ([↔]-intro
            (xy∈f ↦
              ([→]-elim
                ([∀]-elim([∀]-elim([∧]-elimᵣ([∀ₛ]-elim proof{x} (x∈D))) {fnset-witness f(x)}) {y})
                ([∧]-intro
                  ([∀ₛ]-elim(fnset-value f) {x} (x∈D))
                  (xy∈f)
                )
              )
            )

            (fx≡y ↦
              [≡]-elimᵣ (fx≡y) ([∀ₛ]-elim (fnset-value(f)) {x} (x∈D))
            )
          )
        ))
      ))

    [→ₛₑₜ]-witness : ∀{A B} → (f : Domain) → ⦃ _ : Proof(f ∈ (A →ₛₑₜ B)) ⦄ → Function
    [→ₛₑₜ]-witness f ⦃ proof ⦄ (x) =
      (fnset-witness f
        ⦃ [∧]-elimᵣ([↔]-elimᵣ
          ([∀]-elim([∀]-elim filter-containment))
          (proof)
        ) ⦄
        (x)
      )

  module NumeralNaturalProofs where
    open NumeralNatural
    open Structure
    open Structure.Function'.Properties
    open Structure.Relator
    open Structure.Relator.Properties

    [∩]-inductive : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (Inductive(a) ∧ Inductive(b)) ⟶ Inductive(a ∩ b))))
    [∩]-inductive =
      ([∀]-intro (\{a} →
        ([∀]-intro (\{b} →
          ([→]-intro(indaindb ↦
            ([∧]-intro
              -- ∅ is in
              ([↔]-elimₗ
                ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){∅})
                ([∧]-intro
                  ([∧]-elimₗ([∧]-elimₗ indaindb))
                  ([∧]-elimₗ([∧]-elimᵣ indaindb))
                )
              )

              -- 𝐒 is in
              ([∀]-intro (\{x} →
                ([→]-intro(x∈a∩b ↦
                  ([↔]-elimₗ
                    ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){𝐒(x)})
                    ([∧]-intro
                      -- 𝐒(x) ∈ a
                      ([→]-elim([∀]-elim([∧]-elimᵣ([∧]-elimₗ indaindb)){x})(
                        -- x ∈ a
                        [∧]-elimₗ([↔]-elimᵣ
                          ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))

                      -- 𝐒(x) ∈ b
                      ([→]-elim([∀]-elim([∧]-elimᵣ([∧]-elimᵣ indaindb)){x})(
                        -- x ∈ b
                        [∧]-elimᵣ([↔]-elimᵣ
                          ([∀]-elim([∀]-elim([∀]-elim([∩]-containment){a}){b}){x})
                          (x∈a∩b)
                        )
                      ))
                    )
                  )
                ))
              ))
            )
          ))
        ))
      ))

    -- postulate [⋂]-property : ∀{φ} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ φ(x)) ⟶ φ(⋂ s))) TODO: MAybe not true
    [⋂]-inductive : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ s) ⟶ Inductive(x)) ⟶ Inductive(⋂ s)))
    [⋂]-inductive =
      ([∀]-intro (\{s} →
        ([→]-intro(allxxsindx ↦
          ([∧]-intro
            -- ∅ is in
            proof

            -- 𝐒 is in
            proof
          )
        ))
      ))
      where postulate proof : ∀{a} → a

    [ℕ]-inductive : Proof(Inductive(ℕ))
    [ℕ]-inductive =
      ([→]-elim
        ([∀]-elim
          [⋂]-inductive
          {filter(℘(inductiveSet)) Inductive}
        )
        ([∀]-intro(\{x} →
          ([→]-intro(x∈filter ↦
            [∧]-elimᵣ(([↔]-elimᵣ([∀]-elim([∀]-elim filter-containment{℘(inductiveSet)}){x})) (x∈filter))
          ))
        ))
      )

    module _ where
      open Function
      open FunctionProofs

      {- TODO: Something is amiss here? This should only guarantee the existence of a function when the arguments are in ℕ. The problem is probably that FunctionSet may not actually describe a set? See the TODO for FunctionSet. Maybe one should use BoundedFunctionSet instead? But FunctionSet defines a set by using filter, so maybe it is the unique existence to metaobject function that makes this weird?
      postulate [ℕ]-recursive-function : ∀{z : Domain}{s : Domain → Domain → Domain} → Proof(∃ₛ!(ℕ →ₛₑₜ ℕ)(f ↦ ((𝟎 , z) ∈ f) ∧ (∀ₗ(n ↦ ∀ₗ(fn ↦ ((n , fn) ∈ f) ⟶ ((𝐒(n) , s(n)(fn)) ∈ f))))))

      [ℕ]-recursive-function-witness : Domain → BinaryOperator → Function
      [ℕ]-recursive-function-witness z s = fnset-witness([∃ₛ!]-witness ⦃ f ⦄ ) ⦃ [∀ₛ]-elim ([∀]-elim filter-property) ([∃ₛ!]-domain ⦃ f ⦄) ⦄ where
        f = [ℕ]-recursive-function{z}{s}

      _+_ : Domain → Domain → Domain
      _+_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = a

        s : Domain → Domain → Domain
        s(n)(sn) = 𝐒(sn)

      _⋅_ : Domain → Domain → Domain
      _⋅_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝟎

        s : Domain → Domain → Domain
        s(n)(sn) = sn + a

      _^'_ : Domain → Domain → Domain -- TODO: Temporary name collision fix
      _^'_ a b = [ℕ]-recursive-function-witness z s b where
        z : Domain
        z = 𝐒(𝟎)

        s : Domain → Domain → Domain
        s(n)(sn) = sn ⋅ a
      -}

    postulate [ℕ]-elements : Proof(∀ₛ(ℕ)(n ↦ (n ≡ 𝟎) ∨ ∃ₛ(ℕ)(p ↦ n ≡ 𝐒(p))))

    postulate [<]-irreflexivity : Proof(Irreflexivity(ℕ)(_<_))
    postulate [<]-asymmetry     : Proof(Antisymmetry(ℕ)(_<_))
    postulate [<]-transitivity  : Proof(Transitivity(ℕ)(_<_))

    postulate [≤]-reflexivity  : Proof(Irreflexivity(ℕ)(_≤_))
    postulate [≤]-antisymmetry : Proof(Antisymmetry(ℕ)(_≤_))
    postulate [≤]-transitivity : Proof(Transitivity(ℕ)(_≤_))

    instance
      [𝐒]-type : Function.Type(𝐒)
      [𝐒]-type = Function.Type.intro ℕ ℕ proof where
        postulate proof : ∀{a} → a

    postulate [𝐒]-injective : Proof(Injective(𝐒))

    -- ∀ₛ(ℕ)(a ↦ ∀ₛ(ℕ)(b ↦ (a < b) ⟶ (𝐒(a) < 𝐒(b))))
    -- ∀ₛ(ℕ)(n ↦ 𝟎 ≢ 𝐒(n))
