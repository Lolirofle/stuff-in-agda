open import Functional using (id)
import      Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

import      Lvl
open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.BoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation              ⦃ classicLogic ⦄ (_∈_)
open import Type

[⊆]-reflexivity : Proof(∀ₗ(s ↦ s ⊆ s))
[⊆]-reflexivity = [∀].intro(\{_} → [∀].intro(\{_} → [→].reflexivity))

[⊆]-transitivity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ⊆ b)∧(b ⊆ c) ⟶ (a ⊆ c)))))
[⊆]-transitivity =
  ([∀].intro(\{a} →
    ([∀].intro(\{b} →
      ([∀].intro(\{c} →
        ([→].intro(abbc ↦
          ([∀].intro(\{x} →
            ([→].transitivity
              ([∀].elim([∧].elimₗ abbc){x})
              ([∀].elim([∧].elimᵣ abbc){x})
            )
          ))
        ))
      ))
    ))
  ))

record SetEquality : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    extensional : Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ ∀ₗ(x ↦ (x ∈ s₁) ⟷ (x ∈ s₂)) ⟷ (s₁ ≡ s₂))))

  postulate [≡]-from-subset : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ ((x ⊇ y) ∧ (x ⊆ y)) ⟷ (x ≡ y))))

  -- All sets that are defined using an equivalence of contained elements are unique
  unique-definition : ∀{φ : Domain → Formula} → Proof(Unique(S ↦ ∀ₗ(x ↦ (x ∈ S) ⟷ φ(x))))
  unique-definition{_} =
    ([∀].intro(\{S₁} →
      ([∀].intro(\{S₂} →
        ([→].intro(proof ↦
          ([↔].elimᵣ
            ([∀].elim([∀].elim extensional{S₁}){S₂})
            ([∀].intro(\{x} →
              ([↔].transitivity
                ([∀].elim([∧].elimₗ(proof)){x})
                ([↔].commutativity([∀].elim([∧].elimᵣ(proof)){x}))
              )
            ))
          )
        ))
      ))
    ))

  [⊆]-antisymmetry : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a)∧(a ⊆ b) ⟶ (a ≡ b))))
  [⊆]-antisymmetry =
    ([∀].intro(\{a} →
      ([∀].intro(\{b} →
        ([→].intro(abba ↦
          ([↔].elimᵣ([∀].elim([∀].elim extensional{a}){b}))
          ([∀].intro(\{x} →
            ([↔].intro
              ([→].elim([∀].elim([∧].elimₗ abba){x}))
              ([→].elim([∀].elim([∧].elimᵣ abba){x}))
            )
          ))
        ))
      ))
    ))

-- Empty set
-- The set consisting of no elements.
record EmptySet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    ∅ : Domain

  field
    [∅]-inclusion : Proof(∀ₗ(x ↦ x ∉ ∅))

  postulate [⊆]-minimum : Proof(∀ₗ(min ↦ ∀ₗ(s ↦ min ⊆ s) ⟷ (min ≡ ∅)))

  [∅]-inclusion-equiv : Proof(∀ₗ(x ↦ (x ∈ ∅) ⟷ ⊥))
  [∅]-inclusion-equiv =
    ([∀].intro (\{x} →
      ([↔].intro
        ([⊥].elim)
        ([¬].elim
          ([∀].elim [∅]-inclusion{x})
        )
      )
    ))

  [∅]-subset : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [∅]-subset =
    ([∀].intro(\{s} →
      ([∀].intro(\{x} →
        ([→].intro(xin∅ ↦
          [⊥].elim ([↔].elimᵣ([∀].elim [∅]-inclusion-equiv {x}) (xin∅))
        ))
      ))
    ))

  postulate [∅]-subset-is-equal : Proof(∀ₗ(s ↦ (s ⊆ ∅) ⟶ (s ≡ ∅)))
  -- [∅]-subset-is-equal =
  --   ([∀].intro(\{s} →
  --     ([→].intro(s⊆∅ ↦
  --       
  --     ))
  --   ))

  [⊆]-minima : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [⊆]-minima = [∅]-subset

  [∃ₛ]-of-[∅] : ∀{P : Domain → Formula} → Proof(¬(∃ₛ ∅ P))
  [∃ₛ]-of-[∅] =
    ([¬].intro(ep ↦
      [∃ₛ]-elim(\{x} → x∈∅ ↦ _ ↦ [⊥].elim([¬].elim ([∀].elim [∅]-inclusion) x∈∅)) ep
    ))

-- Singleton set.
-- A set consisting of only a single element.
record SingletonSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    singleton : Domain → Domain

  field
    singleton-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(x ↦ (x ∈ singleton(a)) ⟷ (x ≡ a))))

  singleton-contains-self : Proof(∀ₗ(s ↦ s ∈ singleton(s)))
  singleton-contains-self =
    ([∀].intro(\{s} →
      ([↔].elimₗ
        ([∀].elim([∀].elim singleton-inclusion{s}){s})
        ([≡].intro)
      )
    ))

-- Subset filtering.
-- The subset of the specified set where all elements satisfy the specified formula.
record FilterSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    filter : Domain → (Domain → Formula) → Domain

  field
    filter-inclusion : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))

  filter-subset : ∀{φ} → Proof(∀ₗ(s ↦ filter(s)(φ) ⊆ s))
  filter-subset =
    ([∀].intro(\{s} →
      ([∀].intro(\{x} →
        ([→].intro(xinfilter ↦
          [∧].elimₗ([↔].elimᵣ([∀].elim([∀].elim filter-inclusion{s}){x}) (xinfilter))
        ))
      ))
    ))

  module _ ⦃ _ : EmptySet ⦄ ⦃ _ : SetEquality ⦄ where
    open EmptySet ⦃ ... ⦄
    open SetEquality ⦃ ... ⦄

    filter-of-[∅] : ∀{φ} → Proof(filter(∅)(φ) ≡ ∅)
    filter-of-[∅] =
      ([→].elim
        ([∀].elim([∀].elim [⊆]-antisymmetry))
        ([∧].intro
          ([∀].elim [∅]-subset)
          ([∀].elim filter-subset)
        )
      )

  filter-property : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₛ(filter(s)(φ)) φ))
  filter-property =
    ([∀].intro(\{s} →
      ([∀].intro(\{x} →
        ([→].intro(xinfilter ↦
          [∧].elimᵣ([↔].elimᵣ([∀].elim([∀].elim filter-inclusion{s}){x}) (xinfilter))
        ))
      ))
    ))

-- Power set.
-- The set of all subsets of the specified set.
record PowerSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    ℘ : Domain → Domain

  field
    [℘]-inclusion : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))


  module _ ⦃ _ : SetEquality ⦄ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄
    open SetEquality ⦃ ... ⦄

    [℘]-contains-empty : Proof(∀ₗ(s ↦ ∅ ∈ ℘(s)))
    [℘]-contains-empty =
      ([∀].intro(\{s} →
        ([↔].elimₗ
          ([∀].elim([∀].elim [℘]-inclusion{s}){∅})
          ([∀].elim [∅]-subset{s})
        )
      ))

    module _ ⦃ _ : SingletonSet ⦄ where
      open SingletonSet ⦃ ... ⦄

      postulate [℘]-of-[∅] : Proof(℘(∅) ≡ singleton(∅))

  [℘]-contains-self : Proof(∀ₗ(s ↦ s ∈ ℘(s)))
  [℘]-contains-self =
    ([∀].intro(\{s} →
      ([↔].elimₗ
        ([∀].elim([∀].elim [℘]-inclusion{s}){s})
        ([∀].elim [⊆]-reflexivity{s})
      )
    ))

-- Union over arbitrary sets.
-- Constructs a set which consists of elements which are in any of the specified sets.
record SetUnionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    ⋃ : Domain → Domain

  field
    [⋃]-inclusion : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₛ(ss)(s ↦ x ∈ s))))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [⋃]-containing-max : Proof(∀ₗ(s ↦ ∀ₛ(s)(max ↦ ∀ₛ(s)(x ↦ x ⊆ max) ⟶ (⋃(s) ≡ max))))

    module _ ⦃ _ : EmptySet ⦄ where
      open EmptySet ⦃ ... ⦄

      postulate [⋃]-of-[∅] : Proof(⋃(∅) ≡ ∅)
      -- [⋃]-of-[∅] =
      --   ([⋃]-inclusion
      --   )
      --   [∃ₛ]-of-[∅]

  postulate [⋃]-subset : Proof(∀ₗ(s ↦ ∀ₛ(s)(x ↦ x ⊆ ⋃(s))))

-- Union operator.
-- Constructs a set which consists of both elements from LHS and RHS.
record UnionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3000 _∪_
  field
    _∪_ : Domain → Domain → Domain

  field
    [∪]-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∪ b)) ⟷ (x ∈ a)∨(x ∈ b)))))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [∪]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∪ b ≡ b ∪ a)))
    postulate [∪]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∪ b) ∪ c ≡ a ∪ (b ∪ c)))))

    module _ ⦃ _ : EmptySet ⦄ where
      open EmptySet ⦃ ... ⦄

      postulate [∪]-identityₗ : Proof(∀ₗ(s ↦ ∅ ∪ s ≡ s))
      postulate [∪]-identityᵣ : Proof(∀ₗ(s ↦ s ∪ ∅ ≡ s))

  postulate [∪]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ⊆ a ∪ b)))
  postulate [∪]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ b ⊆ a ∪ b)))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [∪]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∪ b ≡ a)))))
    postulate [∪]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∪ b ≡ b)))))
    postulate [∪]-of-self : Proof(∀ₗ(s ↦ s ∪ s ≡ s))


-- Intersection operator.
-- Constructs a set which consists of elements which are in both LHS and RHS.
record IntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3001 _∩_
  field
    _∩_ : Domain → Domain → Domain

  field
    [∩]-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∩ b)) ⟷ (x ∈ a)∧(x ∈ b)))))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [∩]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ≡ b ∩ a)))
    postulate [∩]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∩ b) ∩ c ≡ a ∩ (b ∩ c)))))

    module _ ⦃ _ : EmptySet ⦄ where
      open EmptySet ⦃ ... ⦄

      postulate [∩]-annihilatorₗ : Proof(∀ₗ(s ↦ ∅ ∩ s ≡ ∅))
      postulate [∩]-annihilatorᵣ : Proof(∀ₗ(s ↦ s ∩ ∅ ≡ s))

  postulate [∩]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ a)))
  postulate [∩]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ b)))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [∩]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∩ b ≡ b))))
    postulate [∩]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∩ b ≡ a))))
    postulate [∩]-of-self : Proof(∀ₗ(s ↦ s ∩ s ≡ s))

-- "Without"-operator.
-- Constructs a set which consists of elements which are in LHS, but not RHS.
record WithoutSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3002 _∖_
  field
    _∖_ : Domain → Domain → Domain

  field
    [∖]-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∖ b)) ⟷ (x ∈ a)∧(x ∉ b)))))

-- Intersection over arbitrary sets.
-- Constructs a set which consists of elements which are in all of the specified sets.
record SetIntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    ⋂ : Domain → Domain

  field
    [⋂]-inclusion : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋂(ss)) ⟷ ∀ₛ(ss)(s ↦ x ∈ s))))

  module _ ⦃ _ : SetEquality ⦄ where
    open SetEquality ⦃ ... ⦄

    postulate [⋂]-containing-min : Proof(∀ₗ(s ↦ ∀ₛ(s)(min ↦ ∀ₛ(s)(x ↦ min ⊆ x) ⟶ (⋂(s) ≡ min))))

    module _ ⦃ _ : EmptySet ⦄ where
      open EmptySet ⦃ ... ⦄

      postulate [⋂]-containing-disjoint : Proof(∀ₗ(s ↦ ∃ₛ(s)(a ↦ ∃ₛ(s)(b ↦ Disjoint(a)(b))) ⟶ (⋂(s) ≡ ∅)))
      postulate [⋂]-containing-[∅] : Proof(∀ₗ(s ↦ (∅ ∈ s) ⟶ (⋂(s) ≡ ∅)))

  postulate [⋂]-subset : Proof(∀ₗ(s ↦ ∀ₛ(s)(x ↦ ⋂(s) ⊆ x)))

record TupleSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3002 _⨯_
  field
    -- Set product (Set of tuples) (Cartesian product).
    _⨯_ : Domain → Domain → Domain

    -- Tuple value.
    -- An ordered pair of values.
    _,_ : Domain → Domain → Domain

    -- TODO: Does this help? Maybe not
    -- ∀l∀r∃!x∃!(a∊(l,r)). x ∈ a
    -- ∀l∀r∃!y∀(a∊(l,r)). y ∈ a

    left  : Domain → Domain

    right : Domain → Domain

    swap : Domain → Domain

record QuotientSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    -- Quotient set.
    -- The set of equivalence classes.
    _/_ : Domain → BinaryRelator → Domain

    -- Equivalence class
    -- The set of elements which are equivalent to the specified one.
    [_of_,_] : Domain → Domain → BinaryRelator → Domain

  -- field
    -- [/]-inclusion : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
    -- eqClass-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ∈ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))

  -- module Quotient {T : Domain} {_≅_ : BinaryRelator} ⦃ equivalence : Proof(Structure.Relator.Properties.Equivalence(T)(_≅_)) ⦄ where
  --   open Structure.Relator.Properties

  --   postulate [/]-inclusion : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
  --   postulate [/]-pairwise-disjoint : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
  --   postulate [/]-not-containing-[∅] : Proof(∀ₗ(x ↦ ∅ ∉ (T / (_≅_))))
  --   postulate [/]-cover : Proof(⋃(T / (_≅_)) ≡ T)
  --   postulate eqClass-inclusion : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ∈ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
  --   postulate eqClass-containing-self : Proof(∀ₗ(a ↦ a ∈ [ a of T , (_≅_) ]))
  --   postulate eqClass-nonempty : Proof(∀ₗ(a ↦ NonEmpty([ a of T , (_≅_) ])))
  --   postulate eqClass-equal-disjoint : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ ¬ Disjoint([ a of T , (_≅_) ])([ b of T , (_≅_) ]))))
  --   postulate eqClass-equal-equivalent : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
  --   postulate eqClass-equal-containingₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (b ∈ [ a of T , (_≅_) ]))))
  --   postulate eqClass-equal-containingᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ∈ [ b of T , (_≅_) ]))))
