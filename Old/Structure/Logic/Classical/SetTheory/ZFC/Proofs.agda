open import Functional hiding (Domain)
import      Structure.Logic.Classical.NaturalDeduction
import      Structure.Logic.Classical.SetTheory.ZFC

module Structure.Logic.Classical.SetTheory.ZFC.Proofs {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) ⦃ signature : _ ⦄ ⦃ axioms : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)
open Structure.Logic.Classical.SetTheory.ZFC.Signature {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ {_∈_} (signature)
open Structure.Logic.Classical.SetTheory.ZFC.ZF        {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ {_∈_} ⦃ signature ⦄ (axioms)

open import Lang.Instance
import      Lvl
open import Structure.Logic.Classical.NaturalDeduction.Proofs            ⦃ classicLogic ⦄
open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.Relation                 ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory                          ⦃ classicLogic ⦄ (_∈_)
open        Structure.Logic.Classical.SetTheory.ZFC                      ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Constructive.Functions(Domain)
open import Structure.Logic.Constructive.Functions.Properties ⦃ constructiveLogicSignature ⦄

open SetEquality ⦃ ... ⦄        hiding (extensional)
open SingletonSet ⦃ ... ⦄       hiding (singleton)
open FilterSet ⦃ ... ⦄          hiding (filter)
open PowerSet ⦃ ... ⦄           hiding (℘)
open SetUnionSet ⦃ ... ⦄        hiding (⋃)
open UnionSet ⦃ ... ⦄           hiding (_∪_)
open IntersectionSet ⦃ ... ⦄    hiding (_∩_)
open WithoutSet ⦃ ... ⦄         hiding (_∖_)
open SetIntersectionSet ⦃ ... ⦄ hiding (⋂)

-- All sets are either empty or non-empty.
postulate Empty-excluded-middle : ∀{s} → Proof(Empty(s) ∨ NonEmpty(s))

pair-membership : Proof(∀ₗ(a₁ ↦ ∀ₗ(a₂ ↦ (∀ₗ(x ↦ (x ∈ pair(a₁)(a₂)) ⟷ (x ≡ a₁)∨(x ≡ a₂))))))
pair-membership = pairing

postulate pair-membership-[≡ₛ] : Proof(∀ₗ(a₁ ↦ ∀ₗ(a₂ ↦ (∀ₗ(x ↦ (x ∈ pair(a₁)(a₂)) ⟷ (x ≡ₛ a₁)∨(x ≡ₛ a₂))))))
-- pair-membership-[≡ₛ] = pairing

instance
  setEqualityInstance : SetEquality
  setEqualityInstance = SetEquality.intro extensional

instance
  emptySetInstance : EmptySet
  emptySetInstance = EmptySet.intro ∅ empty

instance
  singletonSetInstance : SingletonSet
  singletonSetInstance = SingletonSet.intro singleton
    ([∀].intro (\{a} →
      ([∀].intro (\{x} →
        [↔].transitivity
          ([∀].elim([∀].elim([∀].elim(pair-membership-[≡ₛ]){a}){a}){x})
          ([↔].intro ([∨].redundancyₗ) ([∨].redundancyᵣ))
      ))
    ))

instance
  filterSetInstance : FilterSet
  filterSetInstance = FilterSet.intro filter comprehension

instance
  powerSetInstance : PowerSet
  powerSetInstance = PowerSet.intro ℘ power

instance
  setUnionSetInstance : SetUnionSet
  setUnionSetInstance = SetUnionSet.intro ⋃ union

instance
  unionSetInstance : UnionSet
  unionSetInstance = UnionSet.intro _∪_
    ([∀].intro (\{a} →
      ([∀].intro (\{b} →
        ([∀].intro (\{x} →
          ([∀].elim([∀].elim [⋃]-membership{pair(a)(b)}){x})
          ⦗ₗ [↔].transitivity ⦘
          ([↔]-with-[∃] (\{s} →
            ([↔]-with-[∧]ₗ ([∀].elim([∀].elim([∀].elim pair-membership{a}){b}){s}))
            ⦗ₗ [↔].transitivity ⦘
            ([∧][∨]-distributivityᵣ)
            ⦗ₗ [↔].transitivity ⦘
            [↔]-with-[∨] ([≡]-substitute-this-is-almost-trivial) ([≡]-substitute-this-is-almost-trivial)
          ))
          ⦗ₗ [↔].transitivity ⦘
          ([↔].intro ([∃]-redundancyₗ) ([∃]-redundancyᵣ))
        ))
      ))
    ))

instance
  intersectionSetInstance : IntersectionSet
  intersectionSetInstance = IntersectionSet.intro _∩_
    ([∀].intro (\{a} →
      ([∀].intro (\{b} →
        ([∀].elim(filter-membership){a})
      ))
    ))

instance
  withoutSetInstance : WithoutSet
  withoutSetInstance = WithoutSet.intro _∖_
    ([∀].intro (\{a} →
      ([∀].intro (\{b} →
        ([∀].elim(filter-membership){a})
      ))
    ))

instance
  setIntersectionSetInstance : SetIntersectionSet
  setIntersectionSetInstance = SetIntersectionSet.intro ⋂
    ([∀].intro (\{ss} →
      ([∀].intro (\{x} →
        ([↔].intro
          -- (⟵)-case
          (allssinssxins ↦
            ([↔].elimₗ
              ([∀].elim([∀].elim filter-membership{⋃(ss)}){x})
              ([∧].intro
                -- x ∈ ⋃(ss)
                ([∨].elim
                  -- Empty(ss) ⇒ _
                  (allyyninss ↦
                    proof -- TODO: But: Empty(ss) ⇒ (ss ≡ ∅) ⇒ ⋃(ss) ≡ ∅ ⇒ (x ∉ ⋃(ss)) ? Maybe use this argument further up instead to prove something like: (⋂(ss) ≡ ∅) ⇒ (x ∉ ∅)
                  )

                  -- NonEmpty(ss) ⇒ _
                  (existsyinss ↦
                    ([∃].elim
                      (\{y} → yinss ↦ (
                        ([↔].elimₗ([∀].elim([∀].elim([⋃]-membership){ss}){x}))
                        ([∃].intro{_}
                          {y}
                          ([∧].intro
                            -- y ∈ ss
                            (yinss)

                            -- x ∈ y
                            ([→].elim
                              ([∀].elim(allssinssxins){y})
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
            ([∀].intro (\{s} →
              ([→].intro (sinss ↦
                ([→].elim
                  ([∀].elim
                    ([∧].elimᵣ
                      ([↔].elimᵣ
                        ([∀].elim
                          ([∀].elim
                            filter-membership
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

-- postulate any : ∀{l}{a : Set(l)} → a

-- TODO: Just used for reference. Remove these lines later
-- ⋂(a) = filter(⋃(ss)) (x ↦ ∀ₗ(a₂ ↦ (a₂ ∈ ss) ⟶ (x ∈ a₂)))
-- filter-membership : ∀{φ : Domain → Formula} → Proof(∀ₗ(s ↦ ∀ₗ(x ↦ ((x ∈ filter(s)(φ)) ⟷ ((x ∈ s) ∧ φ(x))))))
-- [⋃]-membership : Proof(∀ₗ(ss ↦ ∀ₗ(x ↦ (x ∈ ⋃(ss)) ⟷ ∃ₗ(s ↦ (s ∈ ss)∧(x ∈ s)))))


-- [⨯]-membership : Proof(∀ₗ(a ↦ ∀ₗ(b ↦ ∀ₗ(x ↦ (x ∈ (a ⨯ b)) ⟷ ∃ₛ(a)(x₁ ↦ ∃ₛ(b)(x₂ ↦ x ≡ (x₁ , x₂)))))))
-- [⨯]-membership =

-- [⋃][℘]-inverse : Proof(∀ₗ(s ↦ ⋃(℘(s)) ≡ s))

-- TODO: https://planetmath.org/SurjectionAndAxiomOfChoice
