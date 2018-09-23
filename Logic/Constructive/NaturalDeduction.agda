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
  record Implication : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟶_

    field
      _⟶_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → (Proof(X) → Proof(Y)) → Proof(X ⟶ Y)
      elim  : ∀{X Y} → Proof(X ⟶ Y) → Proof(X) → Proof(Y)

    reflexivity : ∀{X} → Proof(X ⟶ X)
    reflexivity = intro id

    transitivity : ∀{X Y Z} → Proof(X ⟶ Y) → Proof(Y ⟶ Z) → Proof(X ⟶ Z)
    transitivity xy yz = intro((elim yz) ∘ (elim xy))

  -- Rules of reversed implication
  record Consequence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟵_

    field
      _⟵_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → (Proof(X) → Proof(Y)) → Proof(Y ⟵ X)
      elim  : ∀{X Y} → Proof(Y ⟵ X) → Proof(X) → Proof(Y)

    reflexivity : ∀{X} → Proof(X ⟵ X)
    reflexivity = intro id

    transitivity : ∀{X Y Z} → Proof(X ⟵ Y) → Proof(Y ⟵ Z) → Proof(X ⟵ Z)
    transitivity xy yz = intro((elim xy) ∘ (elim yz))

  -- Rules of equivalence
  record Equivalence : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1000 _⟷_

    field
      _⟷_ : Stmt → Stmt → Stmt

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
  record Disjunction : Type{ℓₘ Lvl.⊔ ℓ} where
    infixl 1004 _∨_

    field
      _∨_  : Stmt → Stmt → Stmt

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
    field
      instance ⦃ bottom ⦄      : Bottom
      instance ⦃ top ⦄         : Top
      instance ⦃ conjunction ⦄ : Conjunction
      instance ⦃ disjunction ⦄ : Disjunction
      instance ⦃ implication ⦄ : Implication
      instance ⦃ consequence ⦄ : Consequence
      instance ⦃ equivalence ⦄ : Equivalence
      instance ⦃ negation ⦄    : Negation

    open Bottom      (bottom)      using (⊥)   renaming (elim to [⊥]-elim) public
    open Top         (top)         using (⊤)   renaming (intro to [⊤]-intro) public
    open Conjunction (conjunction) using (_∧_) renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction (disjunction) using (_∨_) renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication (implication) using (_⟶_) renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Consequence (consequence) using (_⟵_) renaming (intro to [←]-intro ; elim to [←]-elim) public
    open Equivalence (equivalence) using (_⟷_) renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    (negation)    using (¬_)  renaming (intro to [¬]-intro ; elim to [¬]-elim) public

    module [⊥] = Bottom      (bottom)
    module [⊤] = Top         (top)
    module [∧] = Conjunction (conjunction)
    module [∨] = Disjunction (disjunction)
    module [→] = Implication (implication)
    module [←] = Consequence (consequence)
    module [↔] = Equivalence (equivalence)
    module [¬] = Negation    (negation)

module Predicate {ℓₘₗₛ ℓₘₒₛ ℓₘₗ ℓₘₒ} {Stmt : Type{ℓₘₗₛ Lvl.⊔ ℓₘₒₛ}} {Domain : Type{ℓₘₒₛ}} (Proof : Stmt → Type{ℓₘₗ Lvl.⊔ ℓₘₒ}) where
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
    field
      instance ⦃ propositional ⦄             : PropositionalTheory
      instance ⦃ universalQuantification ⦄   : UniversalQuantification
      instance ⦃ existentialQuantification ⦄ : ExistentialQuantification

    module [∀] = UniversalQuantification   (universalQuantification)
    module [∃] = ExistentialQuantification (existentialQuantification)

    open Propositional.Theory      (propositional)             public
    open UniversalQuantification   (universalQuantification)   using (∀ₗ) renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification (existentialQuantification) using (∃ₗ) renaming (intro to [∃]-intro ; elim to [∃]-elim) public
