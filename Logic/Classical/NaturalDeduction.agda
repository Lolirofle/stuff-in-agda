module Logic.Classical.NaturalDeduction where

open import Functional hiding (Domain)
import      Lvl
open import Type

-- TODO: Maybe it is worth to try and take a more minimal approach? (Less axioms? Is this more practical/impractical?)

-- Theory of classical propositional logic expressed using natural deduction rules
record Propositional {ℓ} : Type{Lvl.𝐒(ℓ)} where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  Stmt : Type{Lvl.𝐒(ℓ)}
  Stmt = Type{ℓ}

  field
    Proof : Stmt → Stmt
    _∧_   : Stmt → Stmt → Stmt
    _⟶_  : Stmt → Stmt → Stmt
    _⟵_  : Stmt → Stmt → Stmt
    _⟷_  : Stmt → Stmt → Stmt
    _∨_   : Stmt → Stmt → Stmt
    ¬_    : Stmt → Stmt
    ⊥     : Stmt
    ⊤     : Stmt

  field
    [∧]-intro : ∀{X Y} → Proof(X) → Proof(Y) → Proof(X ∧ Y)
    [∧]-elimₗ  : ∀{X Y} → Proof(X ∧ Y) → Proof(X)
    [∧]-elimᵣ  : ∀{X Y} → Proof(X ∧ Y) → Proof(Y)

    [→]-intro : ∀{X Y} → Proof(Y) → Proof(X ⟶ Y)
    [→]-elim  : ∀{X Y} → Proof(X) → Proof(X ⟶ Y) → Proof(Y)

    [←]-intro : ∀{X Y} → Proof(Y) → Proof(Y ⟵ X)
    [←]-elim  : ∀{X Y} → Proof(X) → Proof(Y ⟵ X) → Proof(Y)

    [↔]-intro : ∀{X Y} → Proof(X ← Y) → Proof(X → Y) → Proof(X ⟷ Y)
    [↔]-elimₗ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(X ⟵ Y)
    [↔]-elimᵣ  : ∀{X Y} → Proof(X ⟷ Y) → Proof(X ⟶ Y)

    [∨]-introₗ : ∀{X Y} → Proof(X) → Proof(X ∨ Y)
    [∨]-introᵣ : ∀{X Y} → Proof(Y) → Proof(X ∨ Y)
    [∨]-elim  : ∀{X Y Z : Stmt} → Proof(X → Z) → Proof(Y → Z) → Proof(X ∨ Y) → Proof(Z)

    [¬]-intro : ∀{X} → Proof(X → ⊥) → Proof(¬ X)
    [¬]-elim  : ∀{X} → (Proof(¬ X) → Proof(⊥)) → Proof(X)

    [⊥]-intro : ∀{X : Stmt} → Proof(X) → Proof(X → ⊥) → Proof(⊥)
    [⊥]-elim  : ∀{X : Stmt} → Proof(⊥) → Proof(X)

    [⊤]-intro : Proof(⊤)

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
open Propositional ⦃ ... ⦄ public

-- Theory of classical predicate/(first-order) logic expressed using natural deduction rules
record Predicate {ℓₗ ℓₒ} : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    ⦃ propositional ⦄ : Propositional{ℓₗ Lvl.⊔ ℓₒ}
    Metadomain : Type{ℓₒ}
    Domain     : Type{ℓₒ}
    obj : Metadomain → Domain

  field
    ∀ₗ : (Domain → Stmt) → Stmt
    ∃ₗ : (Domain → Stmt) → Stmt

  field
    [∃]-intro : ∀{P : Domain → Stmt}{a} → P(a) → (∃ₗ P)
    [∃]-elim  : ∀{P : Domain → Stmt}{Z : Stmt} → (∀{x : Metadomain} → P(obj(x)) → Z) → (∃ₗ P) → Z

    -- TODO: These are convenient, but it may not actually be possible to construct it constructively? Maybe wrap it inside something?
    {-[∃]-elem  : ∀{P : Domain → Stmt} → (∃ₗ P) → Domain
    [∃]-proof : ∀{P : Domain → Stmt} → (e : ∃ₗ P) → P([∃]-elem(e))-}

    -- TODO: Are these really correct?
    [∀]-intro : ∀{P : Domain → Stmt} → (∀{x : Metadomain} → P(obj(x))) → (∀ₗ P)
    [∀]-elim  : ∀{P : Domain → Stmt} → (∀ₗ P) → (∀{x : Metadomain} → P(obj(x)))
open Predicate ⦃ ... ⦄ public

record PredicateEq {ℓₗ ℓₒ} : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    ⦃ predicate ⦄ : Predicate{ℓₗ}{ℓₒ}

  field
    _≡_ : Domain → Domain → Stmt

  field
    [≡]-intro : ∀{x} → (x ≡ x)
    [≡]-elim  : ∀{P : Domain → Stmt}{a b} → (a ≡ b) → P(a) → P(b)

  -- Definition of uniqueness of a property.
  -- This means that there is at most one element that satisfies this property.
  -- This is similiar to "Injective" for functions, but this is for statements.
  Unique : (Domain → Stmt) → Stmt
  Unique(P) = ∀ₗ(x ↦ ∀ₗ(y ↦ (P(x) ∧ P(y)) ⟶ (x ≡ y)))

  -- Definition of existence of an unique element satisfying a property.
  -- This means that there is one and only one element that satisfies this property.
  ∃ₗ! : (Domain → Stmt) → Stmt
  ∃ₗ!(P) = ((∃ₗ P) ∧ Unique(P))

open PredicateEq ⦃ ... ⦄ public
