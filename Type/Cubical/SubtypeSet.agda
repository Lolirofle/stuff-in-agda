{-# OPTIONS --cubical #-}

module Type.Cubical.SubtypeSet where

-- open import Function.Axioms
open import Functional
open import Logic.Predicate as PTLogic using () renaming ([∃]-intro to intro)
import      Lvl
open import Structure.Function.Domain using (intro ; Inverseₗ ; Inverseᵣ)
open import Structure.Relator.Properties
open import Structure.Type.Identity
--  open import Type.Cubical.Equiv
import      Type.Cubical.Logic as Logic
open import Type.Cubical.Path.Equality
-- open import Type.Cubical.Univalence
open import Type.Cubical
open import Type.Properties.MereProposition
open import Type.Properties.MereProposition.Proofs
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T : Type{ℓ}

module _ where
  {-
  module _ {P Q : T → Type} ⦃ prop-P : ∀{x} → MereProposition{ℓ}(P(x)) ⦄ ⦃ prop-Q : ∀{x} → MereProposition{ℓ}(Q(x)) ⦄ where
    prop-set-extensionalityₗ : Path P Q ← (∀{x} → P(x) ↔ Q(x))
    prop-set-extensionalityₗ pq = functionExtensionalityOn P Q (propositional-extensionalityₗ pq)
  -}

  {-
  module _ {P Q : T → Type} ⦃ prop-P : ∀{x} → MereProposition{ℓ}(P(x)) ⦄ ⦃ prop-Q : ∀{x} → MereProposition{ℓ}(Q(x)) ⦄ where
    prop-set-extensionalityₗ : (P ≡ Q) ← (∀{x} → P(x) ↔ Q(x))
    prop-set-extensionalityₗ pq = functionExtensionalityOn P Q (propositional-extensionalityₗ pq)
  -}

  --data Prop{ℓ} : Type{Lvl.𝐒(ℓ)} where
  --  intro : (T : Type{ℓ}) → ⦃ MereProposition(T) ⦄ → Prop
  Prop = \{ℓ} → PTLogic.∃{Obj = Type{ℓ}} (T ↦ MereProposition(T))

  private variable P Q : Prop{ℓ}

  ⊤ : Prop
  ⊤ = intro(Logic.⊤) ⦃ prop-top ⦄

  ⊥ : Prop
  ⊥ = intro(Logic.⊥) ⦃ prop-bottom ⦄

  ¬_ : Prop{ℓ} → Prop
  ¬(intro A) = intro(Logic.¬ A) ⦃ prop-negation ⦄

  _⟶_ : Prop{ℓ₁} → Prop{ℓ₂} → Prop
  (intro A) ⟶ (intro B) = intro(A → B) ⦃ prop-implication ⦄

  _∨_ : Prop{ℓ₁} → Prop{ℓ₂} → Prop
  (intro A) ∨ (intro B) = intro(A Logic.∨ B)

  _∧_ : Prop{ℓ₁} → Prop{ℓ₂} → Prop
  (intro A) ∧ (intro B) = intro(A Logic.∧ B) ⦃ prop-conjunction ⦄

  ∃ : (T → Prop{ℓ}) → Prop
  ∃ P = intro(Logic.∃(PTLogic.[∃]-witness ∘ P))

  -- ∀ₚ : (T → Prop{ℓ}) → Prop
  -- ∀ₚ P = intro(PTLogic.∀ₗ(PTLogic.[∃]-witness ∘ P)) ⦃ {!prop-universal!} ⦄

  Proof : Prop{ℓ} → Type
  Proof = PTLogic.[∃]-witness

  [⊤]-intro : Proof(⊤)
  [⊤]-intro = Logic.[⊤]-intro

  [∧]-intro : Proof(P) → Proof(Q) → Proof(P ∧ Q)
  [∧]-intro = Logic.[∧]-intro

private variable A B P Q : Type{ℓ}

record SubtypeSet {ℓₑ ℓ} (T : Type{ℓ}) : Type{ℓ Lvl.⊔ Lvl.𝐒(ℓₑ)} where
  constructor filter
  field _∋_ : T → Prop{ℓₑ}
open SubtypeSet using (_∋_) public

{- TODO: When Structure is generalized to arbitrary logic symbols
import      Structure.Set.Names
open        Structure.Set.Names.From-[∋] (_∋_) public
-}

_∈_ : T → SubtypeSet{ℓ}(T) → Prop
_∈_ = swap(_∋_)

_∉_ : T → SubtypeSet{ℓ}(T) → Prop
_∉_ = (¬_) ∘₂ (_∈_)

_∌_ : SubtypeSet{ℓ}(T) → T → Prop
_∌_ = (¬_) ∘₂ (_∋_)

∅ : SubtypeSet(T)
∅ ∋ _ = ⊥

𝐔 : SubtypeSet(T)
𝐔 ∋ _ = ⊤

∁ : SubtypeSet{ℓ}(T) → SubtypeSet(T)
(∁ A) ∋ x = A ∌ x

_∪_ : SubtypeSet{ℓ₁}(T) → SubtypeSet{ℓ₂}(T) → SubtypeSet(T)
(A ∪ B) ∋ x = (A ∋ x) ∨ (B ∋ x)

_∩_ : SubtypeSet{ℓ₁}(T) → SubtypeSet{ℓ₂}(T) → SubtypeSet(T)
(A ∩ B) ∋ x = (A ∋ x) ∧ (B ∋ x)

_∖_ : SubtypeSet{ℓ₁}(T) → SubtypeSet{ℓ₂}(T) → SubtypeSet(T)
(A ∖ B) ∋ x = (A ∋ x) ∧ (B ∌ x)

unmap : (A → B) → SubtypeSet{ℓ}(B) → SubtypeSet(A)
unmap f(A) ∋ x = A ∋ f(x)

-- map : (A → B) → SubtypeSet{ℓ}(A) → SubtypeSet(B)
-- map f(A) ∋ y = ∃(x ↦ (A ∋ x) ∧ (f(x) ≡ y))

-- TODO: Maybe SubtypeSet should require that the witness is a HSet?
-- ⊶ : (A → B) → SubtypeSet(B)
-- (⊶ f) ∋ y = ∃(x ↦ PTLogic.[∃]-intro (f(x) ≡ y) ⦃ {!!} ⦄)
