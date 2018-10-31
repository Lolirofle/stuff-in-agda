import      Lvl
open import Type

module Structure.Logic.Classical.NaturalDeduction {ℓₗ} {Formula : Type{ℓₗ}} {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ}) where

open import Functional hiding (Domain)
import      Structure.Logic.Constructive.NaturalDeduction
private module Constructive = Structure.Logic.Constructive.NaturalDeduction(Proof)

-- TODO: Maybe it is worth to try and take a more minimal approach? (Less axioms? Is this more practical/impractical?)

module Propositional where
  open Constructive.Propositional using
    (
      Conjunction ;
      Disjunction ;
      Implication ;
      Consequence ;
      Equivalence ;
      Bottom      ;
      Top         ;
      Signature
    )
    public

  -- Rules of negation
  record Negation(¬_ : Formula → Formula) {⊥} ⦃ bottom : Bottom(⊥) ⦄ : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
    open Bottom ⦃ ... ⦄
    field
      intro : ∀{X} → (Proof(X) → Proof(⊥)) → Proof(¬ X)
      elim  : ∀{X} → (Proof(¬ X) → Proof(⊥)) → Proof(X)
      [⊥]-intro : ∀{X} → Proof(¬ X) → (Proof(X) → Proof(⊥))

  -- A theory of classical propositional logic expressed using natural deduction rules
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

    open Bottom      (bottom)      using ()          renaming (elim to [⊥]-elim) public
    open Top         (top)         using ()          renaming (intro to [⊤]-intro) public
    open Conjunction (conjunction) using ()          renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction (disjunction) using ()          renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication (implication) using ()          renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Consequence (consequence) using ()          renaming (intro to [←]-intro ; elim to [←]-elim) public
    open Equivalence (equivalence) using ()          renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    (negation)    using ([⊥]-intro) renaming (intro to [¬]-intro ; elim to [¬]-elim) public

    module [⊥] = Bottom      (bottom)
    module [⊤] = Top         (top)
    module [∧] = Conjunction (conjunction)
    module [∨] = Disjunction (disjunction)
    module [→] = Implication (implication)
    module [←] = Consequence (consequence)
    module [↔] = Equivalence (equivalence)
    module [¬] = Negation    (negation)

module _  {ℓₒ} (Domain : Type{ℓₒ}) {ℓₘₒ} {Object : Type{ℓₘₒ}} (obj : Object → Domain) where
  module Predicate where
    open Constructive.Predicate(Domain) (obj) using
      (
        UniversalQuantification ;
        ExistentialQuantification ;
        Signature
      ) public

    -- A theory of classical predicate/(first-order) logic expressed using natural deduction rules
    record Theory ⦃ sign : Signature ⦄ : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      open Signature(sign) hiding (propositional)

      field
        instance ⦃ propositional ⦄             : Propositional.Theory ⦃ Signature.propositional(sign) ⦄
        instance ⦃ universalQuantification ⦄   : UniversalQuantification(∀ₗ)
        instance ⦃ existentialQuantification ⦄ : ExistentialQuantification(∃ₗ)
      open Propositional.Theory(propositional) public

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

  module PredicateEq where
    -- Rules of equality
    record Equality(_≡_ : Domain → Domain → Formula) : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
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
        instance ⦃ predicate ⦄ : Predicate.Signature
        _≡_ : Domain → Domain → Formula
      open Predicate.Signature(predicate) public


    record Theory ⦃ sign : Signature ⦄ : Type{(ℓₘₗ Lvl.⊔ ℓₘₒ) Lvl.⊔ (ℓₗ Lvl.⊔ ℓₒ)} where
      open Signature(sign) hiding (predicate)

      field
        instance ⦃ predicate ⦄ : Predicate.Theory
        instance ⦃ equality ⦄  : Equality(_≡_)
      open Predicate.Theory(predicate) public

      open Equality(equality) using () renaming (intro to [≡]-intro ; elimₗ to [≡]-elimₗ ; elimᵣ to [≡]-elimᵣ) public

      _≢_ : Domain → Domain → Formula
      _≢_ a b = ¬(_≡_ a b)

      -- Definition of uniqueness of a property.
      -- This means that there is at most one element that satisfies this property.
      -- This is similiar to "Injective" for functions, but this is for statements.
      Unique : (Domain → Formula) → Formula
      Unique(P) = ∀ₗ(x ↦ ∀ₗ(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

      -- Definition of existence of an unique element satisfying a property.
      -- This means that there is one and only one element that satisfies this property.
      ∃ₗ! : (Domain → Formula) → Formula
      ∃ₗ! P = ((∃ₗ P) ∧ Unique(P))

      -- These allows the creation of new symbols which points to something which exists and is unique.
      -- TODO: Does this make this theory have no models? For functions, the functions in the meta-theory here (Agda-functions) represent computable things, and all unique existances are not computable. Normally in set theory, one could interpret every (f(x) = y)-formula as ((x,y) ∈ f), so normally it probably works out in the end of the day?
      -- TODO: Maybe these should be separated from the theory?
      field
        [∃]-witness : ∀{P : Domain → Formula} → ⦃ _ : Proof(∃ₗ P) ⦄ → Object
        [∃]-proof   : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ P) ⦄ → Proof(P(obj([∃]-witness{P} ⦃ p ⦄)))

      [∃!]-witness : ∀{P : Domain → Formula} → ⦃ _ : Proof(∃ₗ! P) ⦄ → Object
      [∃!]-witness{P} ⦃ proof ⦄ = [∃]-witness{P} ⦃ [∧]-elimₗ proof ⦄

      [∃!]-proof : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ! P) ⦄ → Proof(P(obj([∃!]-witness{P} ⦃ p ⦄)))
      [∃!]-proof{P} ⦃ proof ⦄ = [∃]-proof{P} ⦃ [∧]-elimₗ proof ⦄

      [∃!]-unique : ∀{P : Domain → Formula} → ⦃ p : Proof(∃ₗ! P) ⦄ → Proof(∀ₗ(x ↦ P(x) ⟶ (x ≡ obj([∃!]-witness{P} ⦃ p ⦄))))
      [∃!]-unique{P} ⦃ proof ⦄ =
        ([∀]-intro(\{x} →
          ([→]-intro(px ↦
            ([→]-elim
              ([∀]-elim([∀]-elim([∧]-elimᵣ proof) {x}) {[∃!]-witness{P} ⦃ proof ⦄})
              ([∧]-intro
                (px)
                ([∃!]-proof{P} ⦃ proof ⦄)
              )
            )
          ))
        ))
