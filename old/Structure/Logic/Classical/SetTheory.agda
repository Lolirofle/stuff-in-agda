open import Functional using (id)
import      Structure.Logic.Classical.NaturalDeduction

module Structure.Logic.Classical.SetTheory {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

import      Lvl
open import Data.Tuple using () renaming (_⨯_ to _⨯ₘ_ ; _,_ to _,ₘ_)
open import Functional using (_∘_)
open import Syntax.Function
open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation                 ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Constructive.Syntax.Algebra                  ⦃ classicLogic ⦄
open import Syntax.Transitivity
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

[⊆]-transitivable : Transitivable(_⊆_)
[⊆]-transitivable = Transitivity-to-Transitivable [⊆]-transitivity

[⊆][≡ₛ]-antisymmetry : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ ((x ⊇ y) ∧ (x ⊆ y)) ⟶ (x ≡ₛ y))))
[⊆][≡ₛ]-antisymmetry =
  ([∀].intro(\{a} →
    ([∀].intro(\{b} →
      ([→].intro(abba ↦
        ([∀].intro(\{x} →
          ([↔].intro
            ([→].elim([∀].elim([∧].elimₗ abba){x}))
            ([→].elim([∀].elim([∧].elimᵣ abba){x}))
          )
        ))
      ))
    ))
  ))

[≡ₛ]-to-[⊆] : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (x ≡ₛ y) ⟶ (x ⊆ y))))
[≡ₛ]-to-[⊆] =
  ([∀].intro(\{x} →
    ([∀].intro(\{y} →
      ([→].intro(x≡y ↦
        ([∀].intro(\{a} →
          [→].intro([↔].elimᵣ([∀].elim x≡y {a}))
        ))
      ))
    ))
  ))

[≡ₛ]-to-[⊇] : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (x ≡ₛ y) ⟶ (x ⊇ y))))
[≡ₛ]-to-[⊇] =
  ([∀].intro(\{x} →
    ([∀].intro(\{y} →
      ([→].intro(x≡y ↦
        ([∀].intro(\{a} →
          [→].intro([↔].elimₗ([∀].elim x≡y {a}))
        ))
      ))
    ))
  ))

[⊆][≡ₛ]-equivalence : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ ((x ⊇ y) ∧ (x ⊆ y)) ⟷ (x ≡ₛ y))))
[⊆][≡ₛ]-equivalence =
  ([∀].intro(\{x} →
    ([∀].intro(\{y} →
      ([↔].intro
        (x≡y ↦
          ([∧].intro
            ([→].elim([∀].elim([∀].elim [≡ₛ]-to-[⊇] {x}){y}) (x≡y))
            ([→].elim([∀].elim([∀].elim [≡ₛ]-to-[⊆] {x}){y}) (x≡y))
          )
        )

        ([→].elim([∀].elim([∀].elim [⊆][≡ₛ]-antisymmetry{x}){y}))
      )
    ))
  ))

[≡ₛ]-reflexivity : Proof(∀ₗ(s ↦ s ≡ₛ s))
[≡ₛ]-reflexivity = [∀].intro(\{_} → [∀].intro(\{_} → [↔].reflexivity))

[≡ₛ]-transitivity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ≡ₛ b)∧(b ≡ₛ c) ⟶ (a ≡ₛ c)))))
[≡ₛ]-transitivity =
  ([∀].intro(\{a} →
    ([∀].intro(\{b} →
      ([∀].intro(\{c} →
        ([→].intro(abbc ↦
          ([∀].intro(\{x} →
            (
              ([∀].elim([∧].elimₗ abbc){x})
              🝖 ([∀].elim([∧].elimᵣ abbc){x})
            )
          ))
        ))
      ))
    ))
  ))

[≡ₛ]-transitivable : Transitivable(_≡ₛ_)
[≡ₛ]-transitivable = Transitivity-to-Transitivable [≡ₛ]-transitivity

[≡ₛ]-symmetry : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ≡ₛ b) ⟶ (b ≡ₛ a))))
[≡ₛ]-symmetry =
  ([∀].intro(\{a} →
    ([∀].intro(\{b} →
      ([→].intro(ab ↦
        ([∀].intro(\{x} →
          ([↔].commutativity
            ([∀].elim ab{x})
          )
        ))
      ))
    ))
  ))

[≡ₛ]-from-equiv : ∀{A B : Domain}{Af Bf : Domain → Formula} → Proof(∀ₗ(x ↦ (x ∈ A) ⟷ Af(x))) → Proof(∀ₗ(x ↦ (x ∈ B) ⟷ Bf(x))) → Proof(∀ₗ(x ↦ Af(x) ⟷ Bf(x))) → Proof(A ≡ₛ B)
[≡ₛ]-from-equiv aeq beq afbf =
  ([∀].intro(\{x} →
    ([↔].transitivity
      ([↔].transitivity
        ([∀].elim aeq)
        ([∀].elim afbf)
      )
      ([↔].commutativity ([∀].elim beq))
    )
  ))

record SetEquality : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    extensional : Proof(∀ₗ(s₁ ↦ ∀ₗ(s₂ ↦ (s₁ ≡ₛ s₂) ⟷ (s₁ ≡ s₂))))

  extensionalᵣ : ∀{s₁ s₂} → Proof(s₁ ≡ₛ s₂) → Proof(s₁ ≡ s₂)
  extensionalᵣ{s₁}{s₂} (proof) = [↔].elimᵣ ([∀].elim([∀].elim extensional{s₁}){s₂}) (proof)

  -- TODO: Use [⊆][≡ₛ]-equivalence
  [≡]-from-subset : Proof(∀ₗ(x ↦ ∀ₗ(y ↦ ((x ⊇ y) ∧ (x ⊆ y)) ⟷ (x ≡ y))))
  [≡]-from-subset =
    ([∀].intro(\{x} →
      ([∀].intro(\{y} →
        ([↔].intro
          (x≡y ↦ [∧].intro
            ([→].elim ([∀].elim ([∀].elim ([≡]-implies-when-reflexive [⊆]-reflexivity) {x}) {y}) (x≡y))
            ([→].elim ([∀].elim ([∀].elim ([≡]-implies-when-reflexive [⊆]-reflexivity) {x}) {y}) (x≡y))
          )

          (lr ↦
            ([↔].elimᵣ
              ([∀].elim([∀].elim extensional{x}){y})
              ([∀].intro(\{a} →
                ([↔].intro
                  ([→].elim([∀].elim([∧].elimₗ(lr)){a}))
                  ([→].elim([∀].elim([∧].elimᵣ(lr)){a}))
                )
              ))
            )
          )
        )
      ))
    )) where
      [≡]-implies-when-reflexive : ∀{_▫_ : Domain → Domain → Formula} → Proof(∀ₗ(x ↦ x ▫ x)) → Proof(∀ₗ(x ↦ ∀ₗ(y ↦ (x ≡ y) ⟶ (x ▫ y))))
      [≡]-implies-when-reflexive {_▫_} ([▫]-reflexivity) =
        ([∀].intro(\{x} →
          ([∀].intro(\{y} →
            ([→].intro(x≡y ↦
              [≡].elimᵣ{x ▫_} (x≡y) ([∀].elim [▫]-reflexivity{x})
            ))
          ))
        ))

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

  -- TODO: Use [⊆][≡ₛ]-antisymmetry
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
    [∅]-membership : Proof(∀ₗ(x ↦ x ∉ ∅))

  [∅]-membership-equiv : Proof(∀ₗ(x ↦ (x ∈ ∅) ⟷ ⊥))
  [∅]-membership-equiv =
    ([∀].intro (\{x} →
      ([↔].intro
        ([⊥].elim)
        ([¬].elim
          ([∀].elim [∅]-membership{x})
        )
      )
    ))

  [∅]-subset : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [∅]-subset =
    ([∀].intro(\{s} →
      ([∀].intro(\{x} →
        ([→].intro(xin∅ ↦
          [⊥].elim ([↔].elimᵣ([∀].elim [∅]-membership-equiv {x}) (xin∅))
        ))
      ))
    ))

  [∅]-subset-is-equal : Proof(∀ₗ(s ↦ (s ⊆ ∅) ⟶ (s ≡ₛ ∅)))
  [∅]-subset-is-equal =
    ([∀].intro(\{s} →
      ([→].intro(s⊆∅ ↦
        ([→].elim
          ([∀].elim([∀].elim [⊆][≡ₛ]-antisymmetry{s}){∅})
          ([∧].intro
            ([∀].elim [∅]-subset{s})
            (s⊆∅)
          )
        )
      ))
    ))

  [⊆]-minimum : Proof(∀ₗ(min ↦ ∀ₗ(s ↦ min ⊆ s) ⟷ (min ≡ₛ ∅)))
  [⊆]-minimum =
    ([∀].intro(\{min} →
      ([↔].intro
        (min≡∅ ↦
          ([∀].intro(\{s} →
            ([→].elim
              ([∀].elim([∀].elim([∀].elim [⊆]-transitivity {min}){∅}){s})
              ([∧].intro
                ([→].elim ([∀].elim([∀].elim [≡ₛ]-to-[⊆] {min}){∅}) (min≡∅))
                ([∀].elim [∅]-subset {s})
              )
            )
          ))
        )

        (asmin⊆s ↦
          ([→].elim
            ([∀].elim [∅]-subset-is-equal{min})
            ([∀].elim asmin⊆s{∅})
          )
        )
      )
    ))

  [⊆]-minima : Proof(∀ₗ(s ↦ ∅ ⊆ s))
  [⊆]-minima = [∅]-subset

  [∃ₛ]-of-[∅] : ∀{P : Domain → Formula} → Proof(¬(∃ₛ ∅ P))
  [∃ₛ]-of-[∅] =
    ([¬].intro(ep ↦
      [∃ₛ]-elim(\{x} → x∈∅ ↦ _ ↦ [⊥].elim([¬].elim ([∀].elim [∅]-membership) x∈∅)) ep
    ))

-- Singleton set.
-- A set consisting of only a single element.
record SingletonSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    singleton : Domain → Domain

  field
    singleton-membership : Proof(∀ₗ(a ↦ ∀ₗ(x ↦ (x ∈ singleton(a)) ⟷ (x ≡ₛ a))))

  singleton-contains-self : Proof(∀ₗ(s ↦ s ∈ singleton(s)))
  singleton-contains-self =
    ([∀].intro(\{s} →
      ([↔].elimₗ
        ([∀].elim([∀].elim singleton-membership{s}){s})
        ([∀].elim [≡ₛ]-reflexivity{s})
      )
    ))

-- Subset filtering.
-- The subset of the specified set where all elements satisfy the specified formula.
record FilterSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    filter : Domain → (Domain → Formula) → Domain

  field
    filter-membership : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))

  filter-subset : ∀{φ} → Proof(∀ₗ(s ↦ filter(s)(φ) ⊆ s))
  filter-subset =
    ([∀].intro(\{s} →
      ([∀].intro(\{x} →
        ([→].intro(xinfilter ↦
          [∧].elimₗ([↔].elimᵣ([∀].elim([∀].elim filter-membership{s}){x}) (xinfilter))
        ))
      ))
    ))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    filter-of-[∅] : ∀{φ} → Proof(filter(∅)(φ) ≡ₛ ∅)
    filter-of-[∅] =
      ([→].elim
        ([∀].elim([∀].elim [⊆][≡ₛ]-antisymmetry))
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
          [∧].elimᵣ([↔].elimᵣ([∀].elim([∀].elim filter-membership{s}){x}) (xinfilter))
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
    [℘]-membership : Proof(∀ₗ(s ↦ ∀ₗ(x ↦ (x ∈ ℘(s)) ⟷ (x ⊆ s))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    [℘]-contains-empty : Proof(∀ₗ(s ↦ ∅ ∈ ℘(s)))
    [℘]-contains-empty =
      ([∀].intro(\{s} →
        ([↔].elimₗ
          ([∀].elim([∀].elim [℘]-membership{s}){∅})
          ([∀].elim [∅]-subset{s})
        )
      ))

    module _ ⦃ _ : SingletonSet ⦄ where
      open SingletonSet ⦃ ... ⦄

      postulate [℘]-of-[∅] : Proof(℘(∅) ≡ₛ singleton(∅))

  [℘]-contains-self : Proof(∀ₗ(s ↦ s ∈ ℘(s)))
  [℘]-contains-self =
    ([∀].intro(\{s} →
      ([↔].elimₗ
        ([∀].elim([∀].elim [℘]-membership{s}){s})
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
    [⋃]-membership : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₛ(ss)(s ↦ x ∈ s))))

  postulate [⋃]-containing-max : Proof(∀ₗ(s ↦ ∀ₛ(s)(max ↦ ∀ₛ(s)(x ↦ x ⊆ max) ⟶ (⋃(s) ≡ₛ max))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    postulate [⋃]-of-[∅] : Proof(⋃(∅) ≡ₛ ∅)
    -- [⋃]-of-[∅] =
    --   ([⋃]-membership
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
    [∪]-membership : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∪ b)) ⟷ (x ∈ a)∨(x ∈ b)))))

  [∪]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∪ b ≡ₛ b ∪ a)))
  [∪]-commutativity =
    ([∀].intro(\{a} →
      ([∀].intro(\{b} →
        ([∀].intro(\{x} →
          ([↔].intro
            (([↔].elimₗ ([∀].elim ([∀].elim ([∀].elim [∪]-membership)))) ∘ [∨].commutativity ∘ ([↔].elimᵣ ([∀].elim ([∀].elim ([∀].elim [∪]-membership)))))
            (([↔].elimₗ ([∀].elim ([∀].elim ([∀].elim [∪]-membership)))) ∘ [∨].commutativity ∘ ([↔].elimᵣ ([∀].elim ([∀].elim ([∀].elim [∪]-membership)))))
          )
        ))
      ))
    ))

  postulate [∪]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∪ b) ∪ c ≡ₛ a ∪ (b ∪ c)))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    postulate [∪]-identityₗ : Proof(∀ₗ(s ↦ ∅ ∪ s ≡ₛ s))
    postulate [∪]-identityᵣ : Proof(∀ₗ(s ↦ s ∪ ∅ ≡ₛ s))

  postulate [∪]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ⊆ a ∪ b)))
  postulate [∪]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ b ⊆ a ∪ b)))
  postulate [∪]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∪ b ≡ₛ a))))
  postulate [∪]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∪ b ≡ₛ b))))
  postulate [∪]-of-self : Proof(∀ₗ(s ↦ s ∪ s ≡ₛ s))

-- Intersection operator.
-- Constructs a set which consists of elements which are in both LHS and RHS.
record IntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3001 _∩_
  field
    _∩_ : Domain → Domain → Domain

  field
    [∩]-membership : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∩ b)) ⟷ (x ∈ a)∧(x ∈ b)))))

  postulate [∩]-commutativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ≡ₛ b ∩ a)))
  postulate [∩]-associativity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(c ↦ (a ∩ b) ∩ c ≡ₛ a ∩ (b ∩ c)))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    postulate [∩]-annihilatorₗ : Proof(∀ₗ(s ↦ ∅ ∩ s ≡ₛ ∅))
    postulate [∩]-annihilatorᵣ : Proof(∀ₗ(s ↦ s ∩ ∅ ≡ₛ s))

  postulate [∩]-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ a)))
  postulate [∩]-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ a ∩ b ⊆ b)))

  postulate [∩]-of-subsetₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (b ⊆ a) ⟶ (a ∩ b ≡ₛ b))))
  postulate [∩]-of-subsetᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ⊆ b) ⟶ (a ∩ b ≡ₛ a))))
  postulate [∩]-of-self : Proof(∀ₗ(s ↦ s ∩ s ≡ₛ s))

-- "Without"-operator.
-- Constructs a set which consists of elements which are in LHS, but not RHS.
record WithoutSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3002 _∖_
  field
    _∖_ : Domain → Domain → Domain

  field
    [∖]-membership : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∖ b)) ⟷ (x ∈ a)∧(x ∉ b)))))

  postulate [∖]-of-disjoint : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ Disjoint(a)(b) ⟶ (a ∖ b ≡ₛ a)))))

  module _ ⦃ _ : IntersectionSet ⦄ where
    open IntersectionSet ⦃ ... ⦄

    postulate [∖]-of-intersection : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ a ∖ (a ∩ b) ≡ₛ a ∖ b))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    postulate [∖]-annihilatorₗ : Proof(∀ₗ(s ↦ ∅ ∖ s ≡ₛ ∅))
    postulate [∖]-identityᵣ : Proof(∀ₗ(s ↦ s ∖ ∅ ≡ₛ s))
    postulate [∖]-subset : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (a ⊆ b) ⟶ (a ∖ b ≡ₛ ∅)))))
    postulate [∖]-of-self : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ a ∖ a ≡ₛ ∅))))

  module _ ⦃ _ : SingletonSet ⦄ where
    open SingletonSet ⦃ ... ⦄

    postulate [∖]-of-singleton : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ∖ singleton(b))) ⟷ (x ∈ a)∧(x ≢ b)))))

-- Intersection over arbitrary sets.
-- Constructs a set which consists of elements which are in all of the specified sets.
record SetIntersectionSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    ⋂ : Domain → Domain

  field
    [⋂]-membership : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋂(ss)) ⟷ ∀ₛ(ss)(s ↦ x ∈ s))))

  postulate [⋂]-containing-min : Proof(∀ₗ(s ↦ ∀ₛ(s)(min ↦ ∀ₛ(s)(x ↦ min ⊆ x) ⟶ (⋂(s) ≡ₛ min))))

  module _ ⦃ _ : EmptySet ⦄ where
    open EmptySet ⦃ ... ⦄

    postulate [⋂]-containing-disjoint : Proof(∀ₗ(s ↦ ∃ₛ(s)(a ↦ ∃ₛ(s)(b ↦ Disjoint(a)(b))) ⟶ (⋂(s) ≡ₛ ∅)))
    postulate [⋂]-containing-[∅] : Proof(∀ₗ(s ↦ (∅ ∈ s) ⟶ (⋂(s) ≡ₛ ∅)))

  postulate [⋂]-subset : Proof(∀ₗ(s ↦ ∀ₛ(s)(x ↦ ⋂(s) ⊆ x)))

-- Set of all sets.
record UniversalSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    𝐔 : Domain

  field
    [𝐔]-membership : Proof(∀ₗ(x ↦ (x ∈ 𝐔)))

  [𝐔]-membership-equiv : Proof(∀ₗ(x ↦ (x ∈ 𝐔) ⟷ ⊤))
  [𝐔]-membership-equiv =
    ([∀].intro(\{x} →
      ([↔].intro
        (_ ↦ [∀].elim [𝐔]-membership)
        (_ ↦ [⊤].intro)
      )
    ))

  [𝐔]-subset : Proof(∀ₗ(x ↦ x ⊆ 𝐔))
  [𝐔]-subset =
    ([∀].intro(\{x} →
      ([∀].intro(\{a} →
        ([→].intro(_ ↦
          [∀].elim [𝐔]-membership
        ))
      ))
    ))

  [𝐔]-superset : Proof(∀ₗ(x ↦ (x ⊇ 𝐔) ⟶ (x ≡ₛ 𝐔)))
  [𝐔]-superset =
    ([∀].intro(\{x} →
      ([→].intro(superset ↦
        ([→].elim
          ([∀].elim ([∀].elim [⊆][≡ₛ]-antisymmetry))
          ([∧].intro
            superset
            ([∀].elim [𝐔]-subset)
          )
        )
      ))
    ))

  [𝐔]-contains-self : Proof(𝐔 ∈ 𝐔)
  [𝐔]-contains-self = [∀].elim [𝐔]-membership

  [𝐔]-nonempty : Proof(∃ₗ(x ↦ (x ∈ 𝐔)))
  [𝐔]-nonempty = [∃].intro [𝐔]-contains-self

  module _ ⦃ _ : FilterSet ⦄ where
    open FilterSet ⦃ ... ⦄

    unrestricted-comprehension-contradiction : Proof(⊥)
    unrestricted-comprehension-contradiction =
      ([∨].elim
        (contains ↦
          ([¬].elim
            ([∧].elimᵣ([↔].elimᵣ
              ([∀].elim([∀].elim filter-membership{𝐔}){not-in-self})
              contains
            ))
            contains
          )
        )

        (contains-not ↦
          ([¬].elim
            (contains-not)
            ([↔].elimₗ
              ([∀].elim([∀].elim filter-membership{𝐔}){not-in-self})
              ([∧].intro
                ([∀].elim [𝐔]-membership {not-in-self})
                (contains-not)
              )
            )
          )
        )

        (excluded-middle{not-in-self ∈ not-in-self})
      ) where
        not-in-self : Domain
        not-in-self = filter(𝐔) (x ↦ (x ∉ x))

record TupleSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  infixl 3002 _⨯_
  field
    -- Set product (Set of tuples) (Cartesian product).
    _⨯_ : Domain → Domain → Domain

    -- Tuple value.
    -- An ordered pair of values.
    _,_ : Domain → Domain → Domain

    left : Domain → Domain

    right : Domain → Domain

  swap : Domain → Domain
  swap(x) = (right(x) , left(x))

  field
    [⨯]-membership : Proof(∀ₗ(A ↦ ∀ₗ(B ↦ ∀ₗ(x ↦ (x ∈ (A ⨯ B)) ⟷ ∃ₛ(A)(a ↦ ∃ₛ(B)(b ↦ x ≡ (a , b))))))) -- TODO: Maybe left and right is not neccessary because one can just take the witnesses of this
    left-equality : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ left(a , b) ≡ a)))
    right-equality : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ right(a , b) ≡ b)))

  postulate [⨯]-tuples : Proof(∀ₗ(A ↦ ∀ₗ(B ↦ ∀ₛ(A)(a ↦ ∀ₛ(B)(b ↦ (a , b) ∈ (A ⨯ B))))))
  postulate swap-equality : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ swap(a , b) ≡ (b , a))))
  postulate left-right-identity : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (left(a , b) , right(a , b)) ≡ (a , b))))

record QuotientSet : Type{ℓₘₗ Lvl.⊔ ℓₗ Lvl.⊔ ℓₒ} where
  constructor intro
  field
    -- Quotient set.
    -- The set of equivalence classes.
    _/_ : Domain → BinaryRelator → Domain

    -- Equivalence class
    -- The set of elements which are equivalent to the specified one.
    [_of_] : Domain → (Domain ⨯ₘ BinaryRelator) → Domain

  field
    [/]-membership : ∀{T}{_≅_} → Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of (T ,ₘ (_≅_)) ]))))
    eqClass-membership : ∀{T}{_≅_} → Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ∈ [ b of (T ,ₘ (_≅_)) ]) ⟷ (a ≅ b))))

  -- module Quotient {T : Domain} {_≅_ : BinaryRelator} ⦃ equivalence : Proof(Structure.Relator.Properties.Equivalence(T)(_≅_)) ⦄ where
  --   open Structure.Relator.Properties

  --   postulate [/]-membership : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
  --   postulate [/]-pairwise-disjoint : Proof(∀ₗ(x ↦ (x ∈ (T / (_≅_))) ⟷ (∃ₗ(y ↦ x ≡ [ y of T , (_≅_) ]))))
  --   postulate [/]-not-containing-[∅] : Proof(∀ₗ(x ↦ ∅ ∉ (T / (_≅_))))
  --   postulate [/]-cover : Proof(⋃(T / (_≅_)) ≡ T)
  --   postulate eqClass-membership : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ (a ∈ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
  --   postulate eqClass-containing-self : Proof(∀ₗ(a ↦ a ∈ [ a of T , (_≅_) ]))
  --   postulate eqClass-nonempty : Proof(∀ₗ(a ↦ NonEmpty([ a of T , (_≅_) ])))
  --   postulate eqClass-equal-disjoint : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ ¬ Disjoint([ a of T , (_≅_) ])([ b of T , (_≅_) ]))))
  --   postulate eqClass-equal-equivalent : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ≅ b))))
  --   postulate eqClass-equal-containingₗ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (b ∈ [ a of T , (_≅_) ]))))
  --   postulate eqClass-equal-containingᵣ : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ([ a of T , (_≅_) ] ≡ [ b of T , (_≅_) ]) ⟷ (a ∈ [ b of T , (_≅_) ]))))
