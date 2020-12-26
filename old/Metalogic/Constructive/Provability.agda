module Metalogic.Constructive.Provability where

open import Sets.BoolSet
open import Functional
import      Lvl
open import Type

  -- Structural rules
record Structural {ℓ ℓₘ} {Formula : Type{ℓ}} (_⊢_ : BoolSet(Formula) → Formula → Type{ℓₘ}) : Type{ℓₘ Lvl.⊔ ℓ} where
  field
    assumption : ∀{Γ}{φ} → (φ ∈ Γ) → (Γ ⊢ φ)

module Propositional {ℓ ℓₘ} {Formula : Type{ℓ}} (_⊢_ : BoolSet(Formula) → Formula → Type{ℓₘ}) where
  -- Rules of bottom
  record Bottom : Type{ℓₘ Lvl.⊔ ℓ} where
    field
      ⊥    : Formula

    field
      intro : ∀{Γ}{φ} → (Γ ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ⊥) → (Γ ⊢ ⊥)
      elim  : ∀{Γ}{φ} → (⊥ ∈ Γ) → (Γ ⊢ φ)

  -- Rules of top
  record Top : Type{ℓₘ Lvl.⊔ ℓ} where
    field
      ⊤    : Formula

    field
      intro : ∀{Γ} → (Γ ⊢ ⊤)

  -- Rules of conjunction
  record Conjunction : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1005 _∧_

    field
      _∧_  : Formula → Formula → Formula

    field
      intro : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → (Γ ⊢ φ₂) → (Γ ⊢ (φ₁ ∧ φ₂))
      elimₗ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ∧ φ₂)) → (Γ ⊢ φ₁)
      elimᵣ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ∧ φ₂)) → (Γ ⊢ φ₂)

  -- Rules of implication
  record Implication : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟶_

    field
      _⟶_ : Formula → Formula → Formula

    field
      intro : ∀{Γ}{φ₁ φ₂} → ((Γ ∪ singleton(φ₁)) ⊢ φ₂) → (Γ ⊢ (φ₁ ⟶ φ₂))
      elim  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ⟶ φ₂)) → (Γ ⊢ φ₁) → (Γ ⊢ φ₂)

  -- Rules of reversed implication
  record Consequence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟵_

    field
      _⟵_ : Formula → Formula → Formula

    field
      intro : ∀{Γ}{φ₁ φ₂} → ((Γ ∪ singleton(φ₁)) ⊢ φ₂) → (Γ ⊢ (φ₂ ⟵ φ₁))
      elim  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₂ ⟵ φ₁)) → (Γ ⊢ φ₁) → (Γ ⊢ φ₂)

  -- Rules of equivalence
  record Equivalence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟷_

    field
      _⟷_ : Formula → Formula → Formula

    field
      intro : ∀{Γ}{φ₁ φ₂} → ((Γ ∪ singleton(φ₂)) ⊢ φ₁) → ((Γ ∪ singleton(φ₁)) ⊢ φ₂) → (Γ ⊢ (φ₁ ⟷ φ₂))
      elimₗ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ⟷ φ₂)) → (Γ ⊢ φ₂) → (Γ ⊢ φ₁)
      elimᵣ  : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ (φ₁ ⟷ φ₂)) → (Γ ⊢ φ₁) → (Γ ⊢ φ₂)

  -- Rules of disjunction
  record Disjunction : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1004 _∨_

    field
      _∨_  : Formula → Formula → Formula

    field
      introₗ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₁) → (Γ ⊢ (φ₁ ∨ φ₂))
      introᵣ : ∀{Γ}{φ₁ φ₂} → (Γ ⊢ φ₂) → (Γ ⊢ (φ₁ ∨ φ₂))
      elim  : ∀{Γ}{φ₁ φ₂ φ₃} → (Γ ⊢ (φ₁ ∨ φ₂)) → ((Γ ∪ singleton(φ₁)) ⊢ φ₃) → ((Γ ∪ singleton(φ₂)) ⊢ φ₃) → (Γ ⊢ φ₃)

  -- Rules of negation
  record Negation ⦃ _ : Bottom ⦄ : Type{ℓₘ Lvl.⊔ ℓ} where
    open Bottom ⦃ ... ⦄

    infixl 1010 ¬_

    field
      ¬_   : Formula → Formula

    field
      intro : ∀{Γ}{φ} → ((Γ ∪ singleton(φ)) ⊢ ⊥) → (Γ ⊢ (¬ φ))
      elim  : ∀{Γ}{φ} → (Γ ⊢ (¬ φ)) → (Γ ⊢ φ) → (Γ ⊢ ⊥)

  -- A theory of constructive propositional logic expressed using natural deduction rules
  record Theory : Type{ℓₘ Lvl.⊔ ℓ} where
    open Structural  ⦃ ... ⦄ public
    open Conjunction ⦃ ... ⦄ renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction ⦃ ... ⦄ renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication ⦃ ... ⦄ renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Consequence ⦃ ... ⦄ renaming (intro to [←]-intro ; elim to [←]-elim) public
    open Equivalence ⦃ ... ⦄ renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    ⦃ ... ⦄ renaming (intro to [¬]-intro ; elim to [¬]-elim) public
    open Bottom      ⦃ ... ⦄ renaming (intro to [⊥]-intro ; elim to [⊥]-elim) public
    open Top         ⦃ ... ⦄ renaming (intro to [⊤]-intro) public

    field
      ⦃ bottom ⦄      : Bottom
      ⦃ top ⦄         : Top
      ⦃ conjunction ⦄ : Conjunction
      ⦃ disjunction ⦄ : Disjunction
      ⦃ implication ⦄ : Implication
      ⦃ consequence ⦄ : Consequence
      ⦃ equivalence ⦄ : Equivalence
      ⦃ negation ⦄    : Negation

module Predicate {ℓₘₗₛ ℓₘₒₛ ℓₘₗ ℓₘₒ} {Formula : Type{ℓₘₗₛ Lvl.⊔ ℓₘₒₛ}} {Domain : Type{ℓₘₒₛ}} (Proof : Formula → Type{ℓₘₗ Lvl.⊔ ℓₘₒ}) (Construct : Domain → Type{ℓₘₒ}) where
  open Propositional(Proof) renaming (Theory to PropositionalTheory)

  record UniversalQuantification : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    field
      ∀ₗ : (Domain → Formula) → Formula

    field
      intro : ∀{P : Domain → Formula} → (∀{x : Domain} → Proof(P(x))) → Proof(∀ₗ P)
      elim  : ∀{P : Domain → Formula} → Proof(∀ₗ P) → (∀{x : Domain} → Proof(P(x)))

  record ExistentialQuantification : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    field
      ∃ₗ : (Domain → Formula) → Formula

    field
      intro : ∀{P : Domain → Formula}{a} → Proof(P(a)) → Proof(∃ₗ P)
      elim  : ∀{P : Domain → Formula}{Z : Formula} → (∀{x : Domain} → Proof(P(x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)

  -- A theory of constructive predicate/(first-order) logic expressed using natural deduction rules
  record Theory  : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    open Propositional.Theory      ⦃ ... ⦄ public
    open UniversalQuantification   ⦃ ... ⦄ renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification ⦃ ... ⦄ renaming (intro to [∃]-intro ; elim to [∃]-elim) public

    field
      ⦃ propositional ⦄             : PropositionalTheory
      ⦃ universalQuantification ⦄   : UniversalQuantification
      ⦃ existentialQuantification ⦄ : ExistentialQuantification
