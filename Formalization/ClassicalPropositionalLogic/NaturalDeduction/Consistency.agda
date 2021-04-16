module Formalization.ClassicalPropositionalLogic.NaturalDeduction.Consistency where

import      Lvl
open import Formalization.ClassicalPropositionalLogic.NaturalDeduction
open import Formalization.ClassicalPropositionalLogic.NaturalDeduction.Proofs
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Functional
open import Logic.Propositional as Logic using (_←_)
open import Logic.Propositional.Theorems as Logic using ()
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open import Type

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable P : Type{ℓₚ}
private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
private variable φ ψ : Formula(P)

Inconsistent : Formulas(P){ℓ} → Type
Inconsistent(Γ) = Γ ⊢ ⊥

Consistent : Formulas(P){ℓ} → Type
Consistent(Γ) = Γ ⊬ ⊥ 



consistency-of-[∪]ₗ : Consistent(Γ₁ ∪ Γ₂) → Consistent(Γ₁)
consistency-of-[∪]ₗ con z = con (weaken-union z)

[⊢]-derivability-inconsistency : (Γ ⊢ φ) Logic.↔ Inconsistent(Γ ∪ singleton(¬ φ))
[⊢]-derivability-inconsistency = Logic.[↔]-intro [¬]-elim ([¬]-intro-converse ∘ [¬¬]-intro)

[⊢]-derivability-consistencyᵣ : Consistent(Γ) → ((Γ ⊢ φ) → Consistent(Γ ∪ singleton(φ)))
[⊢]-derivability-consistencyᵣ con Γφ Γφ⊥ = con([⊥]-intro Γφ ([¬]-intro Γφ⊥))

[⊢]-explosion-inconsistency : (∀{φ} → (Γ ⊢ φ)) Logic.↔ Inconsistent(Γ)
[⊢]-explosion-inconsistency {Γ} = Logic.[↔]-intro (λ z → [⊥]-elim z) (λ z → z)

[⊢]-compose-inconsistency : (Γ ⊢ φ) → Inconsistent(Γ ∪ singleton(φ)) → Inconsistent(Γ)
[⊢]-compose-inconsistency Γφ Γφ⊥ = [⊥]-intro Γφ ([¬]-intro Γφ⊥)

[⊢]-compose-consistency : (Γ ⊢ φ) → Consistent(Γ) → Consistent(Γ ∪ singleton(φ))
[⊢]-compose-consistency Γφ = Logic.contrapositiveᵣ ([⊢]-compose-inconsistency Γφ)

[⊢]-subset-consistency : (Γ₁ ⊆ Γ₂) → (Consistent(Γ₂) → Consistent(Γ₁))
[⊢]-subset-consistency sub con = con ∘ weaken sub

[⊢]-subset-inconsistency : (Γ₁ ⊆ Γ₂) → (Inconsistent(Γ₁) → Inconsistent(Γ₂))
[⊢]-subset-inconsistency sub = weaken sub

[⊬]-negation-consistency : (Γ ⊬ (¬ φ)) → Consistent(Γ ∪ singleton(φ))
[⊬]-negation-consistency = _∘ [¬]-intro

[⊢]-consistent-noncontradicting-membership : Consistent(Γ) → ((¬ φ) ∈ Γ) → (φ ∈ Γ) → Logic.⊥
[⊢]-consistent-noncontradicting-membership con Γ¬φ Γφ = con([⊥]-intro (direct Γφ) (direct Γ¬φ))
