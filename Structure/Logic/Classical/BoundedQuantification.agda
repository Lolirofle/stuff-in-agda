import Structure.Logic.Classical.NaturalDeduction

-- TODO: MAybe rename to PredicateBoundedQuantification
module Structure.Logic.Classical.BoundedQuantification {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} {ℓₘₒ} {Object} {obj} ⦃ sign : _ ⦄ ⦃ theory : _ ⦄ where
private module PredicateEq = Structure.Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₒ} {Object} (obj)
open PredicateEq.Signature(sign) renaming (propositional to propositionalSign)
open PredicateEq.Theory(theory) renaming (propositional to propositionalTheory)

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open import Type.Dependent

-- Bounded universal quantifier
∀ₚ : (Domain → Formula) → (Domain → Formula) → Formula
∀ₚ(B)(P) = ∀ₗ(x ↦ B(x) ⟶ P(x))

[∀ₚ]-intro : ∀{B}{P} → (∀{x} → Proof(B(obj x)) → Proof(P(obj x))) → Proof(∀ₚ(B)(P))
[∀ₚ]-intro {B}{P} proof =
  ([∀]-intro(\{x} →
    ([→]-intro(bx ↦
      proof{x}(bx)
    ))
  ))

[∀ₚ]-elim : ∀{B}{P} → Proof(∀ₚ(B)(P)) → ∀{x} → Proof(B(obj x)) → Proof(P(obj x))
[∀ₚ]-elim {B}{P} allSφ {x} bx =
  ([→]-elim
    ([∀]-elim allSφ{x})
    (bx)
  )

-- Bounded existential quantifier
∃ₚ : (Domain → Formula) → (Domain → Formula) → Formula
∃ₚ(B)(P) = ∃ₗ(x ↦ B(x) ∧ P(x))

[∃ₚ]-intro : ∀{B}{P}{x} → Proof(B(obj x)) → Proof(P(obj x)) → Proof(∃ₚ(B)(P))
[∃ₚ]-intro {B}{P}{x} bx φx =
  ([∃]-intro{_}
    {x}
    ([∧]-intro
      (bx)
      (φx)
    )
  )

[∃ₚ]-elim : ∀{B}{P₁}{P₂} → (∀{x} → Proof(B(obj x)) → Proof(P₁(obj x)) → Proof(P₂)) → Proof(∃ₚ(B)(P₁)) → Proof(P₂)
[∃ₚ]-elim {B}{P₁}{P₂} proof existence =
  ([∃]-elim{_}{P₂}
    (\{x} → conj ↦ (
      (proof
        {x}
        ([∧]-elimₗ(conj))
        ([∧]-elimᵣ(conj))
      )
    ))
    (existence)
  )

[∃ₚ]-to-[∃ₗ] : ∀{B P} → Proof(∃ₚ(B)(P)) → Proof(∃ₗ(P))
[∃ₚ]-to-[∃ₗ] ebp = [∃ₚ]-elim (\{x} → bx ↦ px ↦ [∃]-intro px) (ebp)

[∃ₚ]-witness : ∀{B P} → ⦃ _ : Proof(∃ₚ B P) ⦄ → Object
[∃ₚ]-witness ⦃ proof ⦄ = [∃]-witness ⦃ proof ⦄

[∃ₚ]-bound : ∀{B P} → ⦃ p : Proof(∃ₚ B P) ⦄ → Proof(B(obj([∃ₚ]-witness{B}{P} ⦃ p ⦄)))
[∃ₚ]-bound ⦃ proof ⦄ = [∧]-elimₗ([∃]-proof ⦃ proof ⦄)

[∃ₚ]-proof : ∀{B P} → ⦃ p : Proof(∃ₚ B P) ⦄ → Proof(P(obj([∃ₚ]-witness{B}{P} ⦃ p ⦄)))
[∃ₚ]-proof ⦃ proof ⦄ = [∧]-elimᵣ([∃]-proof ⦃ proof ⦄)

Uniqueₚ : (Domain → Formula) → (Domain → Formula) → Formula
Uniqueₚ(B)(P) = ∀ₚ(B)(x ↦ ∀ₚ(B)(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

-- Bounded unique existential quantifier
∃ₚ! : (Domain → Formula) → (Domain → Formula) → Formula
∃ₚ!(B)(P) = ((∃ₚ(B) P) ∧ Uniqueₚ(B)(P))

[∃ₚ!]-witness : ∀{B P} → ⦃ _ : Proof(∃ₚ! B P) ⦄ → Object
[∃ₚ!]-witness ⦃ proof ⦄ = [∃ₚ]-witness ⦃ [∧]-elimₗ proof ⦄

[∃ₚ!]-bound : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(B(obj([∃ₚ!]-witness{B}{P} ⦃ p ⦄)))
[∃ₚ!]-bound ⦃ proof ⦄ = [∃ₚ]-bound ⦃ [∧]-elimₗ proof ⦄

[∃ₚ!]-proof : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(P(obj([∃ₚ!]-witness{B}{P} ⦃ p ⦄)))
[∃ₚ!]-proof ⦃ proof ⦄ = [∃ₚ]-proof ⦃ [∧]-elimₗ proof ⦄

postulate [∃ₚ!]-unique : ∀{B P} → ⦃ p : Proof(∃ₚ! B P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ obj([∃ₚ!]-witness{B}{P} ⦃ p ⦄))))

-- TODO: This should make it possible to embed a theory inside of another theory (e.g. group theory in set theory), but does not work. How should I formulate something like this for it to work?
instance
  boundedPredEqSignature : (B : Domain → Formula) → Structure.Logic.Classical.NaturalDeduction.Predicate.Signature {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₗ Lvl.⊔ ℓₘₒ} {Σ Object (x ↦ Proof(B(obj x)))} (o ↦ obj(Σ.elem o))
  boundedPredEqSignature(B) =
    record{
      propositional = propositionalSign ;
      ∀ₗ = ∀ₚ(B) ;
      ∃ₗ = ∃ₚ(B)
    }

instance
  boundedPredEqTheory : (B : Domain → Formula) → Proof(∃ₗ B) → Structure.Logic.Classical.NaturalDeduction.Predicate.Theory {ℓₗ} {Formula} {ℓₘₗ} (Proof) {ℓₒ} (Domain) {ℓₘₗ Lvl.⊔ ℓₘₒ} {Σ Object (x ↦ Proof(B(obj x)))} (o ↦ obj(Σ.elem o)) ⦃ boundedPredEqSignature(B) ⦄
  boundedPredEqTheory(B) (eB) =
    record{
      propositional = propositionalTheory ;
      universalQuantification =
        record{
          intro = \{P} → proof ↦ [∀ₚ]-intro{B}{P} (\{x} → bx ↦ proof{Σ.intro x bx}) ;
          elim  = \{P} → ap ↦ \{x} → [∀ₚ]-elim ap{Σ.elem x} (Σ.proof x)
        } ;
      existentialQuantification =
        record{
          intro = \{P}{a} → pa ↦ [∃ₚ]-intro{B}{P}{Σ.elem a} (Σ.proof a) pa;
          elim  = \{P}{Z} → axpxz ↦ ep ↦ [∃ₚ]-elim{B}{P} (\{x} → bx ↦ px ↦ axpxz{Σ.intro x bx}(px)) ep
        } ;
      nonEmptyDomain = [∃]-elim(\{a} → Ba ↦ [∃]-intro([∧]-intro Ba [⊤]-intro)) (eB)
    }
