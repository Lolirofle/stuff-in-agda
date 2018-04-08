module Logic.Constructive.NaturalDeduction where

open import Functional
import      Lvl
open import Type

module Propositional {ℓ ℓₘ} {Stmt : Type{ℓ}} (Proof : Stmt → Type{ℓₘ}) where
  -- Rules of bottom
  record Bottom : Type{ℓₘ Lvl.⊔ ℓ} where
    field
      ⊥    : Stmt

    field
      intro : ∀{X} → Proof(X) → (Proof(X) → Proof(⊥)) → Proof(⊥)
      elim  : ∀{X} → Proof(⊥) → Proof(X)

  -- Rules of top
  record Top : Type{ℓₘ Lvl.⊔ ℓ} where
    field
      ⊤    : Stmt

    field
      intro : Proof(⊤)

  -- Rules of conjunction
  record Conjunction : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1005 _∧_

    field
      _∧_  : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → Proof(X) → Proof(Y) → Proof(X ∧ Y)
      elimₗ  : ∀{X Y} → Proof(X ∧ Y) → Proof(X)
      elimᵣ  : ∀{X Y} → Proof(X ∧ Y) → Proof(Y)

  -- Rules of implication
  record Implication : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟶_

    field
      _⟶_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → Proof(Y) → Proof(X ⟶ Y)
      elim  : ∀{X Y} → Proof(X ⟶ Y) → Proof(X) → Proof(Y)

  -- Rules of reversed implication
  record Consequence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟵_

    field
      _⟵_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → Proof(Y) → Proof(Y ⟵ X)
      elim  : ∀{X Y} → Proof(Y ⟵ X) → Proof(X) → Proof(Y)

  -- Rules of equivalence
  record Equivalence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟷_

    field
      _⟷_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → (Proof(X) ← Proof(Y)) → (Proof(X) → Proof(Y)) → Proof(X ⟷ Y)
      elimₗ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(Y) → Proof(X)
      elimᵣ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(X) → Proof(Y)

  -- Rules of disjunction
  record Disjunction : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1004 _∨_

    field
      _∨_  : Stmt → Stmt → Stmt

    field
      introₗ : ∀{X Y} → Proof(X) → Proof(X ∨ Y)
      introᵣ : ∀{X Y} → Proof(Y) → Proof(X ∨ Y)
      elim  : ∀{X Y Z} → Proof(X ∨ Y) → (Proof(X) → Proof(Z)) → (Proof(Y) → Proof(Z)) → Proof(Z)

  -- Rules of negation
  record Negation ⦃ _ : Bottom ⦄ : Type{ℓₘ Lvl.⊔ ℓ} where
    open Bottom ⦃ ... ⦄

    infixl 1010 ¬_

    field
      ¬_   : Stmt → Stmt

    field
      intro : ∀{X} → (Proof(X) → Proof(⊥)) → Proof(¬ X)
      elim  : ∀{X} → Proof(¬ X) → Proof(X) → Proof(⊥)

  -- A theory of constructive propositional logic expressed using natural deduction rules
  record Theory : Type{ℓₘ Lvl.⊔ ℓ} where
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

module Predicate {ℓₘₗₛ ℓₘₒₛ ℓₘₗ ℓₘₒ} {Stmt : Type{ℓₘₗₛ Lvl.⊔ ℓₘₒₛ}} {Domain : Type{ℓₘₒₛ}} (Proof : Stmt → Type{ℓₘₗ Lvl.⊔ ℓₘₒ}) (Construct : Domain → Type{ℓₘₒ}) where
  open Propositional(Proof) renaming (Theory to PropositionalTheory)

  record UniversalQuantification : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    field
      ∀ₗ : (Domain → Stmt) → Stmt

    field
      intro : ∀{P : Domain → Stmt} → (∀{x : Domain} → Proof(P(x))) → Proof(∀ₗ P)
      elim  : ∀{P : Domain → Stmt} → Proof(∀ₗ P) → (∀{x : Domain} → Proof(P(x)))

  record ExistentialQuantification : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    field
      ∃ₗ : (Domain → Stmt) → Stmt

    field
      intro : ∀{P : Domain → Stmt}{a} → Proof(P(a)) → Proof(∃ₗ P)
      elim  : ∀{P : Domain → Stmt}{Z : Stmt} → (∀{x : Domain} → Proof(P(x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)

  -- A theory of constructive predicate/(first-order) logic expressed using natural deduction rules
  record Theory  : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₘₗₛ Lvl.⊔ ℓₘₒₛ)} where
    open Propositional.Theory      ⦃ ... ⦄ public
    open UniversalQuantification   ⦃ ... ⦄ renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification ⦃ ... ⦄ renaming (intro to [∃]-intro ; elim to [∃]-elim) public

    field
      ⦃ propositional ⦄             : PropositionalTheory
      ⦃ universalQuantification ⦄   : UniversalQuantification
      ⦃ existentialQuantification ⦄ : ExistentialQuantification
