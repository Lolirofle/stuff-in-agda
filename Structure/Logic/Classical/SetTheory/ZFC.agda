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

  -- The statement that the set s can be interpreted as a function with a specified domain and codomain.
  -- The following describes the relation in an inexact notation:
  -- • ∀(x∊A)∀(y∊B). ((x,y) ∈ S) ⇔ (S(x) = y)
  BoundedFunctionSet : Domain → Domain → Domain → Formula
  BoundedFunctionSet(A)(B)(s) = ∀ₛ(A)(x ↦ ∃ₛ!(B)(y ↦ (x , y) ∈ s))

  -- The set of function sets, all sets which can be interpreted as a function.
  _^_ : Domain → Domain → Domain
  B ^ A = filter(℘(A ⨯ B)) (BoundedFunctionSet(A)(B))

  _→ₛₑₜ_ = swap _^_

module Structure where
  -- Structures in meta-functions.
  module Function' where -- TODO: Temporary naming fix with tick
    module Properties ⦃ signature : Signature ⦄ where
      open Function

      Injective : (f : Function) → ⦃ _ : Type(f) ⦄ → Formula
      Injective(f) = ∀ₛ(domain{f})(x ↦ ∀ₛ(domain{f})(y ↦ (f(x) ≡ f(y)) ⟶ (x ≡ y)))

      Surjective : (f : Function) → ⦃ _ : Type(f) ⦄ → Formula
      Surjective(f) = ∀ₛ(codomain{f})(y ↦ ∃ₛ(domain{f})(x ↦ y ≡ f(x)))

      Bijective : (f : Function) → ⦃ _ : Type(f) ⦄ → Formula
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

      Equivalence  : Domain → BinaryRelator → Formula
      Equivalence(S)(_▫_) = Reflexivity(S)(_▫_) ∧ Symmetry(S)(_▫_) ∧ Transitivity(S)(_▫_)

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

  postulate [⊆]-minimum : Proof(∀ₗ(min ↦ ∀ₗ(s ↦ min ⊆ s) ⟷ (min ≡ ∅)))

  [⊆]-reflexivity : Proof(∀ₗ(s ↦ s ⊆ s))
  [⊆]-reflexivity = [∀]-intro(\{_} → [∀]-intro(\{_} → [→].reflexivity))

  [⊆]-antisymmetry : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ⊆ b)∧(b ⊆ a) ⟶ (a ≡ b))))
  [⊆]-antisymmetry =
    ([∀]-intro(\{a} →
      ([∀]-intro(\{b} →
        ([→]-intro(abba ↦
          ([↔]-elimᵣ([∀]-elim([∀]-elim extensional{a}){b}))
          ([∀]-intro(\{x} →
            ([↔]-intro
              ([→]-elim([∀]-elim([∧]-elimᵣ abba){x}))
              ([→]-elim([∀]-elim([∧]-elimₗ abba){x}))
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

  postulate filter-of-[∅] : ∀{φ} → Proof(filter(∅)(φ) ≡ ∅)

  filter-subset : ∀{φ} → Proof(∀ₗ(s ↦ filter(s)(φ) ⊆ s))
  filter-subset =
    ([∀]-intro(\{s} →
      ([∀]-intro(\{x} →
        ([→]-intro(xinfilter ↦
          [∧]-elimₗ([↔]-elimᵣ([∀]-elim([∀]-elim filter-containment{s}){x}) (xinfilter))
        ))
      ))
    ))

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
                    proof -- TODO: Is this really provable? Maybe. filter(∅)(..) = ∅ is an idea?
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

    -- The construction of a meta-function in the meta-logic from a function in the set theory
    fnset-witness : ∀{D} → (f : Domain) → ⦃ _ : Proof(FunctionSet(D)(f)) ⦄ → Function
    fnset-witness f ⦃ proof ⦄ = [∃!]-fn-witness ⦃ [↔]-elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] proof ⦄ where
      [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] : ∀{D : Domain}{P : BinaryRelator} → Proof(∀ₗ(x ↦ ∃ₗ!(y ↦ (x ∈ D) ⟶ P(x)(y))) ⟷ ∀ₛ(D)(x ↦ ∃ₗ!(y ↦ P(x)(y))))
      [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] {D}{P} = [↔]-with-[∀] ([∃!]-unrelatedᵣ-[→]ᵣ)

    -- [→ₛₑₜ]-witness : ∀{A B} → (f : Domain) → ⦃ _ : Proof(f ∈ (A →ₛₑₜ B)) ⦄ → (x : Domain) → ⦃ _ : Proof(x ∈ A) ⦄ → Domain
    -- [→ₛₑₜ]-witness f ⦃ proof ⦄ (x) = (TODO: Maybe prove an equivalence of BoundedFunctionSet for all f in B^A? Would it work?)

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

      [ℕ]-recursive-function-witness : Domain → (Domain → Domain → Domain) → Function
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
