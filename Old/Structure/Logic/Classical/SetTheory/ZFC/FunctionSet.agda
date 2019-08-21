open import Functional hiding (Domain)
import      Structure.Logic.Classical.NaturalDeduction
import      Structure.Logic.Classical.SetTheory.ZFC

module Structure.Logic.Classical.SetTheory.ZFC.FunctionSet {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic : _ ⦄ (_∈_ : Domain → Domain → Formula) ⦃ signature : _ ⦄ where
open Structure.Logic.Classical.NaturalDeduction.ClassicalLogic {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} (classicLogic)
open Structure.Logic.Classical.SetTheory.ZFC.Signature {ℓₗ} {Formula} {ℓₘₗ} {Proof} {ℓₒ} {Domain} ⦃ classicLogic ⦄ {_∈_} (signature)

open import Structure.Logic.Classical.SetTheory.SetBoundedQuantification ⦃ classicLogic ⦄ (_∈_)
open import Structure.Logic.Classical.SetTheory.ZFC.BinaryRelatorSet     ⦃ classicLogic ⦄ (_∈_) ⦃ signature ⦄

-- The set s can be interpreted as a function.
FunctionSet : Domain → Formula
FunctionSet(s) = ∀ₗ(x ↦ Unique(y ↦ (x , y) ∈ s))
-- TODO: Maybe also define something that states ∀ₗ(x ↦ (x ∈ A) ↔ ∃ₗ(y ↦ (x , y) ∈ s)) so that a set representation of a function with domains becomes unique? But I think when (s ∈ (B ^ A)) is satisfied, this is implied? So try to prove that (FunctionSet(f) ∧ Total(A)(f) ∧ (the thing I mentioned earlier)) ↔ (f ∈ (B ^ A))

-- The set s can be interpreted as a function with a specified domain.
-- The following describes the relation to the standard notation of functions:
-- • ∀(x∊A)∀y. ((x,y) ∈ S) ⇔ (S(x) = y)
Total : Domain → Domain → Formula
Total(A)(s) = ∀ₛ(A)(x ↦ ∃ₗ(y ↦ (x , y) ∈ s))

Injective' : Domain → Formula
Injective'(f) = ∀ₗ(y ↦ Unique(x ↦ (x , y) ∈ f))

Surjective' : Domain → Domain → Formula
Surjective'(B)(f) = ∀ₛ(B)(y ↦ ∃ₗ(x ↦ (x , y) ∈ f))

Bijective' : Domain → Domain → Formula
Bijective'(B)(f) =
  Injective'(f)
  ∧ Surjective'(B)(f)

-- The set of total function sets. All sets which can be interpreted as a total function.
_^_ : Domain → Domain → Domain
B ^ A = filter(℘(A ⨯ B)) (f ↦ FunctionSet(f) ∧ Total(A)(f))

_→ₛₑₜ_ = swap _^_

⊷ : Domain → Domain
⊷ = lefts

⊶ : Domain → Domain
⊶ = rights

map' : Domain → Domain → Domain
map' = rightsOfMany

unmap' : Domain → Domain → Domain
unmap' = leftsOfMany

apply-set : Domain → Domain → Domain
apply-set = rightsOf

unapply-set : Domain → Domain → Domain
unapply-set = leftsOf

_∘'_ : Domain → Domain → Domain
_∘'_ f g = filter((⊷ f) ⨯ (⊶ g)) (a ↦ ∃ₗ(x ↦ ∃ₗ(y ↦ ∃ₗ(a₁ ↦ ((a₁ , y) ∈ f) ∧ ((x , a₁) ∈ g)) ∧ (a ≡ (x , y)))))

-- inv : Domain → Domain
-- inv f = filter(?) (yx ↦ ∃ₗ(x ↦ ∃ₗ(y ↦ ((x , y) ∈ f) ∧ (yx ≡ (y , x)))))

module Cardinality where
  -- Injection
  _≼_ : Domain → Domain → Formula
  _≼_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Injective')

  -- Surjection
  _≽_ : Domain → Domain → Formula
  _≽_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Surjective'(b))

  -- Bijection
  _≍_ : Domain → Domain → Formula
  _≍_ (a)(b) = ∃ₛ(a →ₛₑₜ b)(Bijective'(b))

  -- Strict injection
  _≺_ : Domain → Domain → Formula
  _≺_ A B = (A ≼ B) ∧ ¬(A ≍ B)

  -- Strict surjection
  _≻_ : Domain → Domain → Formula
  _≻_ A B = (A ≽ B) ∧ ¬(A ≍ B)

  -- TODO: Definition of a "cardinality object" requires ordinals, which requires axiom of choice
  -- # : Domain → Domain
