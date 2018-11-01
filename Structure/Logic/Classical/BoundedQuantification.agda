import Structure.Logic.Classical.NaturalDeduction

-- TODO: MAybe rename to PredicateBoundedQuantification
module Structure.Logic.Classical.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open import Type.Dependent

-- Bounded universal quantifier
∀ₚ : (Domain → Formula) → (Domain → Formula) → Formula
∀ₚ(B)(P) = ∀ₗ(x ↦ B(x) ⟶ P(x))

[∀ₚ]-intro : ∀{B}{P} → (∀{x} → Proof(B(x)) → Proof(P(x))) → Proof(∀ₚ(B)(P))
[∀ₚ]-intro {B}{P} proof =
  ([∀].intro(\{x} →
    ([→].intro(bx ↦
      proof{x}(bx)
    ))
  ))

[∀ₚ]-elim : ∀{B}{P} → Proof(∀ₚ(B)(P)) → ∀{x} → Proof(B(x)) → Proof(P(x))
[∀ₚ]-elim {B}{P} allSφ {x} bx =
  ([→].elim
    ([∀].elim allSφ{x})
    (bx)
  )

-- Bounded existential quantifier
∃ₚ : (Domain → Formula) → (Domain → Formula) → Formula
∃ₚ(B)(P) = ∃ₗ(x ↦ B(x) ∧ P(x))

[∃ₚ]-intro : ∀{B}{P}{x} → Proof(B(x)) → Proof(P(x)) → Proof(∃ₚ(B)(P))
[∃ₚ]-intro {B}{P}{x} bx φx =
  ([∃].intro{_}
    {x}
    ([∧].intro
      (bx)
      (φx)
    )
  )

[∃ₚ]-elim : ∀{B}{P₁}{P₂} → (∀{x} → Proof(B(x)) → Proof(P₁(x)) → Proof(P₂)) → Proof(∃ₚ(B)(P₁)) → Proof(P₂)
[∃ₚ]-elim {B}{P₁}{P₂} proof existence =
  ([∃].elim{_}{P₂}
    (\{x} → conj ↦ (
      (proof
        {x}
        ([∧].elimₗ(conj))
        ([∧].elimᵣ(conj))
      )
    ))
    (existence)
  )

[∃ₚ]-to-[∃ₗ] : ∀{B P} → Proof(∃ₚ(B)(P)) → Proof(∃ₗ(P))
[∃ₚ]-to-[∃ₗ] ebp = [∃ₚ]-elim (\{x} → bx ↦ px ↦ [∃].intro px) (ebp)

[∃ₚ]-witness : ∀{B P} → ⦃ _ : Proof(∃ₚ B P) ⦄ → Domain
[∃ₚ]-witness ⦃ proof ⦄ = [∃]-witness ⦃ proof ⦄

[∃ₚ]-bound : ∀{B P} → ⦃ p : Proof(∃ₚ B P) ⦄ → Proof(B([∃ₚ]-witness{B}{P} ⦃ p ⦄))
[∃ₚ]-bound ⦃ proof ⦄ = [∧].elimₗ([∃]-proof ⦃ proof ⦄)

[∃ₚ]-proof : ∀{B P} → ⦃ p : Proof(∃ₚ B P) ⦄ → Proof(P([∃ₚ]-witness{B}{P} ⦃ p ⦄))
[∃ₚ]-proof ⦃ proof ⦄ = [∧].elimᵣ([∃]-proof ⦃ proof ⦄)

Uniqueₚ : (Domain → Formula) → (Domain → Formula) → Formula
Uniqueₚ(B)(P) = ∀ₚ(B)(x ↦ ∀ₚ(B)(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

-- Bounded unique existential quantifier
∃ₚ! : (Domain → Formula) → (Domain → Formula) → Formula
∃ₚ!(B)(P) = ((∃ₚ(B) P) ∧ Uniqueₚ(B)(P))

[∃ₚ!]-witness : ∀{B P} → ⦃ _ : Proof(∃ₚ! B P) ⦄ → Domain
[∃ₚ!]-witness ⦃ proof ⦄ = [∃ₚ]-witness ⦃ [∧].elimₗ proof ⦄

[∃ₚ!]-bound : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(B([∃ₚ!]-witness{B}{P} ⦃ p ⦄))
[∃ₚ!]-bound ⦃ proof ⦄ = [∃ₚ]-bound ⦃ [∧].elimₗ proof ⦄

[∃ₚ!]-proof : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(P([∃ₚ!]-witness{B}{P} ⦃ p ⦄))
[∃ₚ!]-proof ⦃ proof ⦄ = [∃ₚ]-proof ⦃ [∧].elimₗ proof ⦄

postulate [∃ₚ!]-unique : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ [∃ₚ!]-witness{B}{P} ⦃ p ⦄)))

-- boundedClassicalLogicSignature : 

-- TODO: This should make it possible to embed a theory inside of another theory (e.g. group theory in set theory), but does not work. How should I formulate something like this for it to work?
{-
module _ (B : Domain → Formula) {ℓₒ₂} {Domain₂} (dom : Domain₂ → Domain) (dom-proof : ∀{x} → Proof(B(dom(x)))) (dom⁻¹ : Domain → Domain₂) where
  instance
    boundedPredEqSignature : Structure.Logic.Classical.NaturalDeduction.Domained.Predicate.Signature {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ₂} (Domain₂)
    boundedPredEqSignature =
      record{
        ∀ₗ = P ↦ ∀ₚ(B) (x ↦ P(dom⁻¹ x)) ;
        ∃ₗ = P ↦ ∃ₚ(B) (x ↦ P(dom⁻¹ x))
      }

  instance
    boundedPredEqTheory : Structure.Logic.Classical.NaturalDeduction.Domained.Predicate.Theory {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ₂} (Domain₂) ⦃ boundedPredEqSignature ⦄
    boundedPredEqTheory =
      record{
        universalQuantification =
          record{
            intro = \{P} → proof ↦ [∀ₚ]-intro{B}{P ∘ dom⁻¹} (\{x} → bx ↦ proof{dom⁻¹ x}) ;
            elim  = \{P} → ap ↦ \{x} → [∀ₚ]-elim ap{dom x} (dom-proof{x})
          } ;
        existentialQuantification =
          record{
            intro = \{P}{a} → pa ↦ [∃ₚ]-intro{B}{P}{dom a} (dom-proof{a}) pa;
            elim  = \{P}{Z} → axpxz ↦ ep ↦ [∃ₚ]-elim{B}{P} (\{x} → bx ↦ px ↦ axpxz{dom⁻¹ x}(px)) ep
          }
      }
-}
