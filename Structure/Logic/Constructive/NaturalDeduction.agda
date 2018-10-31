import      Lvl
open import Type

module Structure.Logic.Constructive.NaturalDeduction {ℓₗ} {Formula : Type{ℓₗ}} {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ}) where

open import Functional

module Propositional where
  -- Rules of bottom
  record Bottom(⊥ : Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      elim  : ∀{X} → Proof(⊥) → Proof(X)

  -- Rules of top
  record Top(⊤ : Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      intro : Proof(⊤)

  -- Rules of conjunction
  record Conjunction(_∧_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      intro : ∀{X Y} → Proof(X) → Proof(Y) → Proof(X ∧ Y)
      elimₗ  : ∀{X Y} → Proof(X ∧ Y) → Proof(X)
      elimᵣ  : ∀{X Y} → Proof(X ∧ Y) → Proof(Y)

    redundancyₗ : ∀{X} → Proof(X ∧ X) ← Proof(X)
    redundancyₗ x = intro x x

    redundancyᵣ : ∀{X} → Proof(X ∧ X) → Proof(X)
    redundancyᵣ = elimₗ

    transitivity : ∀{X Y Z} → Proof(X ∧ Y) → Proof(Y ∧ Z) → Proof(X ∧ Z)
    transitivity xy yz = intro(elimₗ xy) (elimᵣ yz)

    commutativity : ∀{X Y} → Proof(X ∧ Y) → Proof(Y ∧ X)
    commutativity xy = intro(elimᵣ xy) (elimₗ xy)

    associativityₗ : ∀{X Y Z} → Proof((X ∧ Y) ∧ Z) ← Proof(X ∧ (Y ∧ Z))
    associativityₗ xyz = intro (intro (elimₗ xyz) (elimₗ(elimᵣ xyz))) (elimᵣ(elimᵣ xyz))

    associativityᵣ : ∀{X Y Z} → Proof((X ∧ Y) ∧ Z) → Proof(X ∧ (Y ∧ Z))
    associativityᵣ xyz = intro (elimₗ(elimₗ xyz)) (intro (elimᵣ(elimₗ xyz)) (elimᵣ xyz))

  -- Rules of implication
  record Implication(_⟶_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      intro : ∀{X Y} → (Proof(X) → Proof(Y)) → Proof(X ⟶ Y)
      elim  : ∀{X Y} → Proof(X ⟶ Y) → Proof(X) → Proof(Y)

    reflexivity : ∀{X} → Proof(X ⟶ X)
    reflexivity = intro id

    transitivity : ∀{X Y Z} → Proof(X ⟶ Y) → Proof(Y ⟶ Z) → Proof(X ⟶ Z)
    transitivity xy yz = intro((elim yz) ∘ (elim xy))

  -- Rules of reversed implication
  record Consequence(_⟵_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      intro : ∀{X Y} → (Proof(X) → Proof(Y)) → Proof(Y ⟵ X)
      elim  : ∀{X Y} → Proof(Y ⟵ X) → Proof(X) → Proof(Y)

    reflexivity : ∀{X} → Proof(X ⟵ X)
    reflexivity = intro id

    transitivity : ∀{X Y Z} → Proof(X ⟵ Y) → Proof(Y ⟵ Z) → Proof(X ⟵ Z)
    transitivity xy yz = intro((elim xy) ∘ (elim yz))

  -- Rules of equivalence
  record Equivalence(_⟷_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      intro : ∀{X Y} → (Proof(X) ← Proof(Y)) → (Proof(X) → Proof(Y)) → Proof(X ⟷ Y)
      elimₗ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(Y) → Proof(X)
      elimᵣ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(X) → Proof(Y)

    reflexivity : ∀{X} → Proof(X ⟷ X)
    reflexivity = intro id id

    commutativity : ∀{X Y} → Proof(X ⟷ Y) → Proof(Y ⟷ X)
    commutativity xy = intro(elimᵣ xy) (elimₗ xy)

    transitivity : ∀{X Y Z} → Proof(X ⟷ Y) → Proof(Y ⟷ Z) → Proof(X ⟷ Z)
    transitivity xy yz = intro ((elimₗ xy) ∘ (elimₗ yz)) ((elimᵣ yz) ∘ (elimᵣ xy))

  -- Rules of disjunction
  record Disjunction(_∨_  : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    field
      introₗ : ∀{X Y} → Proof(X) → Proof(X ∨ Y)
      introᵣ : ∀{X Y} → Proof(Y) → Proof(X ∨ Y)
      elim  : ∀{X Y Z} → (Proof(X) → Proof(Z)) → (Proof(Y) → Proof(Z)) → Proof(X ∨ Y) → Proof(Z)

    redundancyₗ : ∀{X} → Proof(X ∨ X) ← Proof(X)
    redundancyₗ = introₗ

    redundancyᵣ : ∀{X} → Proof(X ∨ X) → Proof(X)
    redundancyᵣ = elim id id

    commutativity : ∀{X Y} → Proof(X ∨ Y) → Proof(Y ∨ X)
    commutativity = elim(introᵣ)(introₗ)

    associativityₗ : ∀{X Y Z} → Proof((X ∨ Y) ∨ Z) ← Proof(X ∨ (Y ∨ Z))
    associativityₗ = elim(introₗ ∘ introₗ) (elim (introₗ ∘ introᵣ) (introᵣ))

    associativityᵣ : ∀{X Y Z} → Proof((X ∨ Y) ∨ Z) → Proof(X ∨ (Y ∨ Z))
    associativityᵣ = elim(elim (introₗ) (introᵣ ∘ introₗ)) (introᵣ ∘ introᵣ)

  -- Rules of negation
  record Negation(¬_ : Formula → Formula) {⊥} ⦃ _ : Bottom(⊥) ⦄ : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    open Bottom ⦃ ... ⦄
    field
      intro : ∀{X} → (Proof(X) → Proof(⊥)) → Proof(¬ X)
      elim  : ∀{X} → Proof(¬ X) → Proof(X) → Proof(⊥)

  record Signature : Type{ℓₗ} where
    infixl 1005 _∧_
    infixl 1000 _⟶_
    infixl 1000 _⟵_
    infixl 1000 _⟷_
    infixl 1004 _∨_
    infixl 1010 ¬_

    field
      ⊥    : Formula
      ⊤    : Formula
      _∧_  : Formula → Formula → Formula
      _⟶_ : Formula → Formula → Formula
      _⟵_ : Formula → Formula → Formula
      _⟷_ : Formula → Formula → Formula
      _∨_  : Formula → Formula → Formula
      ¬_   : Formula → Formula

  -- A theory of constructive propositional logic expressed using natural deduction rules
  record Theory ⦃ sign : Signature ⦄ : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    open Signature(sign)

    field
      instance ⦃ bottom ⦄      : Bottom(⊥)
      instance ⦃ top ⦄         : Top(⊤)
      instance ⦃ conjunction ⦄ : Conjunction(_∧_)
      instance ⦃ disjunction ⦄ : Disjunction(_∨_)
      instance ⦃ implication ⦄ : Implication(_⟶_)
      instance ⦃ consequence ⦄ : Consequence(_⟵_)
      instance ⦃ equivalence ⦄ : Equivalence(_⟷_)
      instance ⦃ negation ⦄    : Negation(¬_) ⦃ bottom ⦄

    open Bottom      (bottom)      using () renaming (elim to [⊥]-elim) public
    open Top         (top)         using () renaming (intro to [⊤]-intro) public
    open Conjunction (conjunction) using () renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction (disjunction) using () renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication (implication) using () renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Consequence (consequence) using () renaming (intro to [←]-intro ; elim to [←]-elim) public
    open Equivalence (equivalence) using () renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    (negation)    using () renaming (intro to [¬]-intro ; elim to [¬]-elim) public

    module [⊥] = Bottom      (bottom)
    module [⊤] = Top         (top)
    module [∧] = Conjunction (conjunction)
    module [∨] = Disjunction (disjunction)
    module [→] = Implication (implication)
    module [←] = Consequence (consequence)
    module [↔] = Equivalence (equivalence)
    module [¬] = Negation    (negation)

module Predicate {ℓₒ} (Domain : Type{ℓₒ}) {ℓₘₒ} {Object : Type{ℓₘₒ}} (obj : Object → Domain) where
  record UniversalQuantification(∀ₗ : (Domain → Formula) → Formula) : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      intro : ∀{P : Domain → Formula} → (∀{x : Object} → Proof(P(obj x))) → Proof(∀ₗ P)
      elim  : ∀{P : Domain → Formula} → Proof(∀ₗ P) → (∀{x : Object} → Proof(P(obj x)))

  record ExistentialQuantification(∃ₗ : (Domain → Formula) → Formula) : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      intro : ∀{P : Domain → Formula}{a} → Proof(P(obj a)) → Proof(∃ₗ P)
      elim  : ∀{P : Domain → Formula}{Z : Formula} → (∀{x : Object} → Proof(P(obj x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)



  record Signature : Type{ℓₗ Lvl.⊔ ℓₒ} where
    field
      instance ⦃ propositional ⦄ : Propositional.Signature
      ∀ₗ : (Domain → Formula) → Formula
      ∃ₗ : (Domain → Formula) → Formula
    open Propositional.Signature(propositional) public

  -- A theory of constructive predicate/(first-order) logic expressed using natural deduction rules
  record Theory ⦃ sign : Signature ⦄ : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Signature(sign) hiding (propositional)

    field
      instance ⦃ propositional ⦄             : Propositional.Theory
      instance ⦃ universalQuantification ⦄   : UniversalQuantification(∀ₗ)
      instance ⦃ existentialQuantification ⦄ : ExistentialQuantification(∃ₗ)
    open Propositional.Theory(propositional) public

    module [∀] = UniversalQuantification   (universalQuantification)
    module [∃] = ExistentialQuantification (existentialQuantification)

    open UniversalQuantification   (universalQuantification)   using () renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification (existentialQuantification) using () renaming (intro to [∃]-intro ; elim to [∃]-elim) public

module MultiSortedPredicate {ℓₒ} {Sorts : Type{ℓₒ}} (Domain : Sorts → Type{ℓₒ}) {ℓₘₒ} {Object : Sorts → Type{ℓₘₒ}} (obj : ∀{Sort} → Object(Sort) → Domain(Sort)) where
  record UniversalQuantification(∀ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula) : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      intro : ∀{Sort}{P : Domain(Sort) → Formula} → (∀{x : Object(Sort)} → Proof(P(obj x))) → Proof(∀ₗ P)
      elim  : ∀{Sort}{P : Domain(Sort) → Formula} → Proof(∀ₗ P) → (∀{x : Object(Sort)} → Proof(P(obj x)))

  record ExistentialQuantification(∃ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula) : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      intro : ∀{Sort}{P : Domain(Sort) → Formula}{a} → Proof(P(obj a)) → Proof(∃ₗ P)
      elim  : ∀{Sort}{P : Domain(Sort) → Formula}{Z : Formula} → (∀{x : Object(Sort)} → Proof(P(obj x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)



  record Signature : Type{ℓₗ Lvl.⊔ ℓₒ} where
    field
      instance ⦃ propositional ⦄ : Propositional.Signature
      ∀ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula
      ∃ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula
    open Propositional.Signature(propositional) public

  -- A theory of constructive predicate/(first-order) multi-sorted logic expressed using natural deduction rules
  record Theory ⦃ sign : Signature ⦄ : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Signature(sign) hiding (propositional)

    field
      instance ⦃ propositional ⦄             : Propositional.Theory ⦃ Signature.propositional(sign) ⦄
      instance ⦃ universalQuantification ⦄   : UniversalQuantification(∀ₗ)
      instance ⦃ existentialQuantification ⦄ : ExistentialQuantification(∃ₗ)
    open Propositional.Theory(propositional) public

    module [∀] = UniversalQuantification   (universalQuantification)
    module [∃] = ExistentialQuantification (existentialQuantification)

    open UniversalQuantification   (universalQuantification)   using () renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification (existentialQuantification) using () renaming (intro to [∃]-intro ; elim to [∃]-elim) public
