import      Lvl
open import Type

module Structure.Logic.Classical.NaturalDeduction {ℓₗ} {Formula : Type{ℓₗ}} {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ}) where

open import Functional hiding (Domain)
import      Structure.Logic.Constructive.NaturalDeduction
private module Constructive = Structure.Logic.Constructive.NaturalDeduction(Proof)

-- TODO: Maybe it is worth to try and take a more minimal approach? (Less axioms? Is this more practical/impractical?)

module Propositional where
  open Constructive.Propositional hiding (Theory) public

  -- A theory of classical propositional logic expressed using natural deduction rules
  record Theory ⦃ sign : Signature ⦄ : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    open Signature(sign)

    field
      instance ⦃ constructive ⦄ : Constructive.Propositional.Theory ⦃ sign ⦄

    open Constructive.Propositional.Theory (constructive) public

    field
      excluded-middle : ∀{P} → Proof(P ∨ (¬ P))

module Domained = Constructive.Domained

module MultiSorted = Constructive.MultiSorted

  {-
  Propositional-from-[∧][∨][⊥] : ∀{ℓₗ} → (_∧_ _∨_ : Formula → Formula → Formula) → (⊥ : Formula) →
    ([∧]-intro : ∀{X Y} → X → Y → (X ∧ Y)) →
    ([∧]-elimₗ  : ∀{X Y} → (X ∧ Y) → X) →
    ([∧]-elimᵣ  : ∀{X Y} → (X ∧ Y) → Y) →
    ([∨]-introₗ : ∀{X Y} → X → (X ∨ Y)) →
    ([∨]-introᵣ : ∀{X Y} → Y → (X ∨ Y)) →
    ([∨]-elim  : ∀{X Y Z : Formula} → (X → Z) → (Y → Z) → (X ∨ Y) → Z) →
    ([⊥]-intro : ∀{X : Formula} → X → (X → ⊥) → ⊥) →
    ([⊥]-elim  : ∀{X : Formula} → ⊥ → X) →
    Propositional{ℓₗ}
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

module _ {ℓₒ} (Domain : Type{ℓₒ}) where
  record ClassicalLogicSignature : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Domained(Domain)

    field
      instance ⦃ propositionalSignature ⦄ : Propositional.Signature
      instance ⦃ predicateSignature ⦄     : Predicate.Signature
      instance ⦃ equalitySignature ⦄      : Equality.Signature

    constructiveLogicSignature : Constructive.ConstructiveLogicSignature(Domain)
    constructiveLogicSignature =
      record{
        propositionalSignature = propositionalSignature ;
        predicateSignature     = predicateSignature ;
        equalitySignature      = equalitySignature
      }

    open Propositional.Signature(propositionalSignature) public
    open Predicate.Signature(predicateSignature) public
    open Equality.Signature(equalitySignature) public
    open Equality.PropositionallyDerivedSignature ⦃ propositionalSignature ⦄ ⦃ equalitySignature ⦄ public
    open Uniqueness.Signature ⦃ propositionalSignature ⦄ ⦃ predicateSignature ⦄ ⦃ equalitySignature ⦄ public

  -- A theory of classical predicate/(first-order) logic expressed using natural deduction rules
  record ClassicalLogic : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Domained(Domain)

    field
      instance ⦃ classicalLogicSignature ⦄ : ClassicalLogicSignature
    open ClassicalLogicSignature(classicalLogicSignature) public

    field
      instance ⦃ propositionalTheory ⦄ : Propositional.Theory ⦃ propositionalSignature ⦄
      instance ⦃ predicateTheory ⦄     : Predicate.Theory
      instance ⦃ equalityTheory ⦄      : Equality.Theory
      instance ⦃ existentialWitness ⦄  : Predicate.ExistentialWitness(∃ₗ)
      ⦃ nonEmptyDomain ⦄               : NonEmptyDomain

    constructivePropositionalTheory = Propositional.Theory.constructive(propositionalTheory)

    constructiveLogic : Constructive.ConstructiveLogic(Domain)
    constructiveLogic =
      record{
        constructiveLogicSignature = constructiveLogicSignature ;
        propositionalTheory        = constructivePropositionalTheory ;
        predicateTheory            = predicateTheory ;
        equalityTheory             = equalityTheory
      }

    open Propositional.Theory(propositionalTheory) public
    open Predicate.Theory(predicateTheory) public
    open Equality.Theory(equalityTheory) public
    open Predicate.ExistentialWitness(existentialWitness) public
    open Uniqueness.WitnessTheory ⦃ propositionalSignature ⦄ ⦃ predicateSignature ⦄ ⦃ equalitySignature ⦄ ⦃ constructivePropositionalTheory ⦄ ⦃ predicateTheory ⦄ ⦃ equalityTheory ⦄ ⦃ existentialWitness ⦄ public
    open NonEmptyDomain ⦃ nonEmptyDomain ⦄ public
