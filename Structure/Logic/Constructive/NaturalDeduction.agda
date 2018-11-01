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

    module [⊥] = Bottom      (bottom)
    module [⊤] = Top         (top)
    module [∧] = Conjunction (conjunction)
    module [∨] = Disjunction (disjunction)
    module [→] = Implication (implication)
    module [←] = Consequence (consequence)
    module [↔] = Equivalence (equivalence)
    module [¬] = Negation    (negation)

module Domained {ℓₒ} (Domain : Type{ℓₒ}) where
  module Predicate where
    record UniversalQuantification(∀ₗ : (Domain → Formula) → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        intro : ∀{P : Domain → Formula} → (∀{x : Domain} → Proof(P(x))) → Proof(∀ₗ P)
        elim  : ∀{P : Domain → Formula} → Proof(∀ₗ P) → (∀{x : Domain} → Proof(P(x)))

    record ExistentialQuantification(∃ₗ : (Domain → Formula) → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        intro : ∀{P : Domain → Formula}{a} → Proof(P(a)) → Proof(∃ₗ P)
        elim  : ∀{P : Domain → Formula}{Z : Formula} → (∀{x : Domain} → Proof(P(x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)

    -- These allows the creation of new symbols which points to something which exists and is unique.
    -- TODO: Does this make this theory have no models? For functions, the functions in the meta-theory here (Agda-functions) represent computable things, and all unique existances are not computable. Normally in set theory, one could interpret every (f(x) = y)-formula as ((x,y) ∈ f), so normally it probably works out in the end of the day?
    record ExistentialWitness(∃ₗ : (Domain → Formula) → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        [∃]-witness : ∀{P : Domain → Formula} → ⦃ _ : Proof(∃ₗ P) ⦄ → Domain
        [∃]-proof   : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ P) ⦄ → Proof(P([∃]-witness{P} ⦃ p ⦄))



    record Signature : Type{ℓₗ Lvl.⊔ ℓₒ} where
      field
        ∀ₗ : (Domain → Formula) → Formula
        ∃ₗ : (Domain → Formula) → Formula

      NonEmptyDomain = ∀{P} → Proof(P) → Proof(∃ₗ(const P))

    -- A theory of constructive predicate/(first-order) logic expressed using natural deduction rules
    record Theory ⦃ sign : Signature ⦄ : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      open Signature(sign)

      field
        instance ⦃ universalQuantification ⦄   : UniversalQuantification(∀ₗ)
        instance ⦃ existentialQuantification ⦄ : ExistentialQuantification(∃ₗ)

      module [∀] = UniversalQuantification   (universalQuantification)
      module [∃] = ExistentialQuantification (existentialQuantification)

      module NonEmptyDomain ⦃ nonEmptyDomain : NonEmptyDomain ⦄ where
        [∀]-redundancyₗ : ∀{φ} → Proof(∀ₗ(const φ)) ← Proof(φ)
        [∀]-redundancyₗ (proof) = [∀].intro(\{_} → proof)

        [∀]-redundancyᵣ : ∀{φ} → Proof(∀ₗ(const φ)) → Proof(φ)
        [∀]-redundancyᵣ (proof) = [∃].elim(\{x} → _ ↦ [∀].elim(proof){x}) (nonEmptyDomain proof)

        [∃]-redundancyₗ : ∀{φ} → Proof(∃ₗ(const φ)) ← Proof(φ)
        [∃]-redundancyₗ (proof) = [∃].elim(\{x} → _ ↦ [∃].intro{_}{x}(proof)) (nonEmptyDomain proof)

        [∃]-redundancyᵣ : ∀{φ} → Proof(∃ₗ(const φ)) → Proof(φ)
        [∃]-redundancyᵣ = [∃].elim(\{_} → id)

  module Equality where
    -- Rules of equality
    record Equality(_≡_ : Domain → Domain → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        intro : ∀{x} → Proof(x ≡ x)
        elimᵣ  : ∀{P : Domain → Formula}{a b} → Proof(a ≡ b) → Proof(P(a)) → Proof(P(b))

      symmetry : ∀{a b} → Proof(a ≡ b) → Proof(b ≡ a)
      symmetry{a} (proof) = elimᵣ{x ↦ x ≡ a} (proof) (intro{a})

      elimₗ : ∀{P : Domain → Formula}{a b} → Proof(a ≡ b) → Proof(P(a)) ← Proof(P(b))
      elimₗ (proof) (pb) = elimᵣ (symmetry proof) (pb)

      transitivity : ∀{a b c} → Proof(a ≡ b) → Proof(b ≡ c) → Proof(a ≡ c)
      transitivity (ab) (bc) = elimᵣ bc ab



    record Signature : Type{ℓₗ Lvl.⊔ ℓₒ} where
      infixl 2000 _≡_
      field
        _≡_ : Domain → Domain → Formula

    module PropositionallyDerivedSignature ⦃ propositional : Propositional.Signature ⦄ ⦃ sign : Signature ⦄ where
      open Propositional.Signature(propositional)
      open Signature(sign)

      _≢_ : Domain → Domain → Formula
      _≢_ a b = ¬(_≡_ a b)

    record Theory ⦃ sign : Signature ⦄ : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      open Signature(sign)

      field
        instance ⦃ equality ⦄ : Equality(_≡_)

      module [≡] = Equality(equality)

  module Uniqueness ⦃ propositionalSign : Propositional.Signature ⦄ ⦃ predicateSign : Predicate.Signature ⦄ ⦃ equalitySign : Equality.Signature ⦄ where
    open Propositional.Signature(propositionalSign)
    open Predicate.Signature(predicateSign)
    open Equality.Signature(equalitySign)

    module Signature where
      -- Definition of uniqueness of a property.
      -- This means that there is at most one element that satisfies this property.
      -- This is similiar to "Injective" for functions, but this is for statements.
      Unique : (Domain → Formula) → Formula
      Unique(P) = ∀ₗ(x ↦ ∀ₗ(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

      -- Definition of existence of an unique element satisfying a property.
      -- This means that there is one and only one element that satisfies this property.
      ∃ₗ! : (Domain → Formula) → Formula
      ∃ₗ! P = ((∃ₗ P) ∧ Unique(P))

    module _ ⦃ propositional : Propositional.Theory ⦄ ⦃ predicate : Predicate.Theory ⦄ ⦃ equality : Equality.Theory ⦄ where
      open Signature
      open Propositional.Theory(propositional)
      open Predicate.Theory(predicate)
      open Equality.Theory(equality)

      module WitnessTheory ⦃ existentialWitness : Predicate.ExistentialWitness(∃ₗ) ⦄ where
        open Predicate.ExistentialWitness(existentialWitness)

        [∃!]-witness : ∀{P : Domain → Formula} → ⦃ _ : Proof(∃ₗ! P) ⦄ → Domain
        [∃!]-witness{P} ⦃ proof ⦄ = [∃]-witness{P} ⦃ [∧].elimₗ proof ⦄

        [∃!]-proof : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ! P) ⦄ → Proof(P([∃!]-witness{P} ⦃ p ⦄))
        [∃!]-proof{P} ⦃ proof ⦄ = [∃]-proof{P} ⦃ [∧].elimₗ proof ⦄

        [∃!]-unique : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ! P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ [∃!]-witness{P} ⦃ p ⦄)))
        [∃!]-unique{P} ⦃ proof ⦄ =
          ([∀].intro(\{x} →
            ([→].intro(px ↦
              ([→].elim
                ([∀].elim([∀].elim([∧].elimᵣ proof) {x}) {[∃!]-witness{P} ⦃ proof ⦄})
                ([∧].intro
                  (px)
                  ([∃!]-proof{P} ⦃ proof ⦄)
                )
              )
            ))
          ))

module _ {ℓₒ} (Domain : Type{ℓₒ}) where
  record ConstructiveLogicSignature : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Domained(Domain)

    field
      instance ⦃ propositionalSignature ⦄ : Propositional.Signature
      instance ⦃ predicateSignature ⦄     : Predicate.Signature
      instance ⦃ equalitySignature ⦄      : Equality.Signature
    open Propositional.Signature(propositionalSignature) public
    open Predicate.Signature(predicateSignature) public
    open Equality.Signature(equalitySignature) public
    open Equality.PropositionallyDerivedSignature ⦃ propositionalSignature ⦄ ⦃ equalitySignature ⦄ public
    open Uniqueness.Signature ⦃ propositionalSignature ⦄ ⦃ predicateSignature ⦄ ⦃ equalitySignature ⦄ public

  record ConstructiveLogic : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
    open Domained(Domain)

    field
      instance ⦃ constructiveLogicSignature ⦄ : ConstructiveLogicSignature
    open ConstructiveLogicSignature public

    field
      instance ⦃ propositionalTheory ⦄ : Propositional.Theory
      instance ⦃ predicateTheory ⦄     : Predicate.Theory
      instance ⦃ equalityTheory ⦄      : Equality.Theory
    open Propositional.Theory(propositionalTheory) public
    open Predicate.Theory(predicateTheory) public
    open Equality.Theory(equalityTheory) public

module MultiSorted {ℓₒ} {Sorts : Type{ℓₒ}} (Domain : Sorts → Type{ℓₒ}) where
  module Predicate where
    record UniversalQuantification(∀ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        intro : ∀{Sort}{P : Domain(Sort) → Formula} → (∀{x : Domain(Sort)} → Proof(P(x))) → Proof(∀ₗ P)
        elim  : ∀{Sort}{P : Domain(Sort) → Formula} → Proof(∀ₗ P) → (∀{x : Domain(Sort)} → Proof(P(x)))

    record ExistentialQuantification(∃ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula) : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      field
        intro : ∀{Sort}{P : Domain(Sort) → Formula}{a} → Proof(P(a)) → Proof(∃ₗ P)
        elim  : ∀{Sort}{P : Domain(Sort) → Formula}{Z : Formula} → (∀{x : Domain(Sort)} → Proof(P(x)) → Proof(Z)) → Proof(∃ₗ P) → Proof(Z)



    record Signature : Type{ℓₗ Lvl.⊔ ℓₒ} where
      field
        ∀ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula
        ∃ₗ : ∀{Sort} → (Domain(Sort) → Formula) → Formula

    -- A theory of constructive predicate/(first-order) multi-sorted logic expressed using natural deduction rules
    record Theory ⦃ sign : Signature ⦄ : Type{ℓₘₗ Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      open Signature(sign)

      field
        instance ⦃ universalQuantification ⦄   : UniversalQuantification(∀ₗ)
        instance ⦃ existentialQuantification ⦄ : ExistentialQuantification(∃ₗ)

      module [∀] = UniversalQuantification   (universalQuantification)
      module [∃] = ExistentialQuantification (existentialQuantification)
