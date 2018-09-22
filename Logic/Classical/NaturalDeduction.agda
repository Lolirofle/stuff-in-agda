module Logic.Classical.NaturalDeduction where

open import Functional hiding (Domain)
import      Lvl
open import Type
import      Logic.Constructive.NaturalDeduction as Constructive

-- TODO: Maybe it is worth to try and take a more minimal approach? (Less axioms? Is this more practical/impractical?)

module Propositional {ℓ ℓₘ} {Stmt : Type{ℓ}} (Proof : Stmt → Type{ℓₘ}) where
  open Constructive.Propositional {ℓ}{ℓₘ} {Stmt} (Proof) using
    (
      Conjunction ;
      Disjunction ;
      Implication ;
      Consequence ;
      Equivalence ;
      Bottom      ;
      Top
    )
    public

  -- Rules of negation
  record Negation ⦃ bottom : Bottom ⦄ : Type{ℓₘ Lvl.⊔ ℓ} where
    open Bottom ⦃ ... ⦄

    infixl 1010 ¬_

    field
      ¬_   : Stmt → Stmt

    field
      intro : ∀{X} → (Proof(X) → Proof(⊥ ⦃ bottom ⦄)) → Proof(¬ X)
      elim  : ∀{X} → (Proof(¬ X) → Proof(⊥ ⦃ bottom ⦄)) → Proof(X)
      [⊥]-intro : ∀{X} → Proof(¬ X) → (Proof(X) → Proof(⊥ ⦃ bottom ⦄))

  -- A theory of classical propositional logic expressed using natural deduction rules
  record Theory : Type{ℓₘ Lvl.⊔ ℓ} where
    field
      instance ⦃ bottom ⦄      : Bottom
      instance ⦃ top ⦄         : Top
      instance ⦃ conjunction ⦄ : Conjunction
      instance ⦃ disjunction ⦄ : Disjunction
      instance ⦃ implication ⦄ : Implication
      instance ⦃ consequence ⦄ : Consequence
      instance ⦃ equivalence ⦄ : Equivalence
      instance ⦃ negation ⦄    : Negation ⦃ bottom ⦄

    open Bottom      (bottom)      using (⊥)   renaming (elim to [⊥]-elim) public
    open Top         (top)         using (⊤)   renaming (intro to [⊤]-intro) public
    open Conjunction (conjunction) using (_∧_) renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction (disjunction) using (_∨_) renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication (implication) using (_⟶_) renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Consequence (consequence) using (_⟵_) renaming (intro to [←]-intro ; elim to [←]-elim) public
    open Equivalence (equivalence) using (_⟷_) renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    (negation)    using (¬_ ; [⊥]-intro)  renaming (intro to [¬]-intro ; elim to [¬]-elim) public

    module [⊥] = Bottom      (bottom)
    module [⊤] = Top         (top)
    module [∧] = Conjunction (conjunction)
    module [∨] = Disjunction (disjunction)
    module [→] = Implication (implication)
    module [←] = Consequence (consequence)
    module [↔] = Equivalence (equivalence)
    module [¬] = Negation    (negation)

module Predicate {ℓₗ ℓₒ ℓₘₗ ℓₘₒ} {Stmt : Type{ℓₗ Lvl.⊔ ℓₒ}} {Domain : Type{ℓₒ}} (Proof : Stmt → Type{ℓₘₗ Lvl.⊔ ℓₘₒ}) (Construct : Domain → Type{ℓₘₒ}) where
  open Propositional(Proof) renaming (Theory to PropositionalTheory)

  open Constructive.Predicate {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) (Construct) using
    (
      UniversalQuantification ;
      ExistentialQuantification
    ) public

  -- A theory of classical predicate/(first-order) logic expressed using natural deduction rules
  record Theory  : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      instance ⦃ propositional ⦄             : PropositionalTheory
      instance ⦃ universalQuantification ⦄   : UniversalQuantification
      instance ⦃ existentialQuantification ⦄ : ExistentialQuantification

    open PropositionalTheory       (propositional)             public
    open UniversalQuantification   (universalQuantification)   renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification (existentialQuantification) renaming (intro to [∃]-intro ; elim to [∃]-elim) public

    field
      ⦃ nonEmptyDomain ⦄ : Proof(∃ₗ(const ⊤))

    module [∀] where
      redundancyₗ : ∀{φ} → Proof(∀ₗ(const φ)) ← Proof(φ)
      redundancyₗ (proof) = [∀]-intro(\{_} → proof)

      redundancyᵣ : ∀{φ} → Proof(∀ₗ(const φ)) → Proof(φ)
      redundancyᵣ (proof) = [∃]-elim(\{x} → _ ↦ [∀]-elim(proof){x}) (nonEmptyDomain)

      open UniversalQuantification(universalQuantification) public

    module [∃] where
      redundancyₗ : ∀{φ} → Proof(∃ₗ(const φ)) ← Proof(φ)
      redundancyₗ (proof) = [∃]-elim(\{x} → _ ↦ [∃]-intro{_}{x}(proof)) (nonEmptyDomain)

      redundancyᵣ : ∀{φ} → Proof(∃ₗ(const φ)) → Proof(φ)
      redundancyᵣ = [∃]-elim(\{_} → id)

      open ExistentialQuantification(existentialQuantification) public
{-
Propositional-from-[∧][∨][⊥] : ∀{ℓ} → (_∧_ _∨_ : Stmt → Stmt → Stmt) → (⊥ : Stmt) →
  ([∧]-intro : ∀{X Y} → X → Y → (X ∧ Y)) →
  ([∧]-elimₗ  : ∀{X Y} → (X ∧ Y) → X) →
  ([∧]-elimᵣ  : ∀{X Y} → (X ∧ Y) → Y) →
  ([∨]-introₗ : ∀{X Y} → X → (X ∨ Y)) →
  ([∨]-introᵣ : ∀{X Y} → Y → (X ∨ Y)) →
  ([∨]-elim  : ∀{X Y Z : Stmt} → (X → Z) → (Y → Z) → (X ∨ Y) → Z) →
  ([⊥]-intro : ∀{X : Stmt} → X → (X → ⊥) → ⊥) →
  ([⊥]-elim  : ∀{X : Stmt} → ⊥ → X) →
  Propositional{ℓ}
Propositional-from-[∧][∨][⊥]
  (_∧_) (_∨_) (⊥)
  ([∧]-intro)
  ([∧]-elimₗ)
  ([∧]-elimᵣ)
  ([∨]-introₗ)
  ([∨]-introᵣ)
  ([∨]-elim)
  ([⊥]-intro)
  ([⊥]-elim)
  = record{
    _∧_  = _∧_ ;
    _∨_  = _∨_ ;
    _⟶_ = (x ↦ y ↦ (x ∨ (¬ y))) ;
    _⟵_ = swap _⟶_ ;
    _⟷_ = (x ↦ y ↦ ((x ⟵ y)∧(x ⟶ y))) ;
    ¬_   = (x ↦ (x ⟶ ⊥)) ;
    ⊥    = ⊥ ;
    ⊤    = ¬ ⊥
  }
-}

module PredicateEq {ℓₗ ℓₒ ℓₘₗ ℓₘₒ} {Stmt : Type{ℓₗ Lvl.⊔ ℓₒ}} {Domain : Type{ℓₒ}} (Proof : Stmt → Type{ℓₘₗ Lvl.⊔ ℓₘₒ}) (Construct : Domain → Type{ℓₘₒ}) where
  open Predicate {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof)(Construct) renaming (Theory to PredicateTheory)

  -- Rules of equality
  record Equality : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    infixl 2000 _≡_

    field
      _≡_ : Domain → Domain → Stmt

    field
      intro : ∀{x} → Proof(x ≡ x)
      elimₗ  : ∀{P : Domain → Stmt}{a b} → Proof(a ≡ b) → Proof(P(a)) ← Proof(P(b))
      elimᵣ  : ∀{P : Domain → Stmt}{a b} → Proof(a ≡ b) → Proof(P(a)) → Proof(P(b))

  record Theory : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    field
      instance ⦃ predicate ⦄ : PredicateTheory
      instance ⦃ equality ⦄  : Equality

    open PredicateTheory (predicate) public
    open Equality        (equality)  renaming (intro to [≡]-intro ; elimₗ to [≡]-elimₗ ; elimᵣ to [≡]-elimᵣ) public

    -- Definition of uniqueness of a property.
    -- This means that there is at most one element that satisfies this property.
    -- This is similiar to "Injective" for functions, but this is for statements.
    Unique : (Domain → Stmt) → Stmt
    Unique(P) = ∀ₗ(x ↦ ∀ₗ(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

    -- Definition of existence of an unique element satisfying a property.
    -- This means that there is one and only one element that satisfies this property.
    ∃ₗ! : (Domain → Stmt) → Stmt
    ∃ₗ! P = ((∃ₗ P) ∧ Unique(P))
