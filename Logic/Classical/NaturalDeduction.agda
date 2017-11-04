module Logic.Classical.NaturalDeduction where

open import Functional
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
    _∧_  : Stmt → Stmt → Stmt
    _⟶_ : Stmt → Stmt → Stmt
    _⟵_ : Stmt → Stmt → Stmt
    _⟷_ : Stmt → Stmt → Stmt
    _∨_  : Stmt → Stmt → Stmt
    ¬_   : Stmt → Stmt
    ⊥    : Stmt
    ⊤    : Stmt

  field
    [∧]-intro : ∀{X Y} → X → Y → (X ∧ Y)
    [∧]-elimₗ  : ∀{X Y} → (X ∧ Y) → X
    [∧]-elimᵣ  : ∀{X Y} → (X ∧ Y) → Y

    [→]-intro : ∀{X Y} → Y → (X ⟶ Y)
    [→]-elim  : ∀{X Y} → X → (X ⟶ Y) → Y

    [←]-intro : ∀{X Y} → Y → (Y ⟵ X)
    [←]-elim  : ∀{X Y} → X → (Y ⟵ X) → Y

    [↔]-intro : ∀{X Y} → (X ← Y) → (X → Y) → (X ⟷ Y)
    [↔]-elimₗ  : ∀{X Y} → (X ⟷ Y) → (X ⟵ Y)
    [↔]-elimᵣ  : ∀{X Y} → (X ⟷ Y) → (X ⟶ Y)

    [∨]-introₗ : ∀{X Y} → X → (X ∨ Y)
    [∨]-introᵣ : ∀{X Y} → Y → (X ∨ Y)
    [∨]-elim  : ∀{X Y Z : Stmt} → (X → Z) → (Y → Z) → (X ∨ Y) → Z

    [¬]-intro : ∀{X} → (X → ⊥) → (¬ X)
    [¬]-elim  : ∀{X} → ((¬ X) → ⊥) → X

    [⊥]-intro : ∀{X : Stmt} → X → (X → ⊥) → ⊥
    [⊥]-elim  : ∀{X : Stmt} → ⊥ → X

    [⊤]-intro : ⊤
open Propositional ⦃ ... ⦄ public

-- Theory of classical predicate/(first-order) logic expressed using natural deduction rules
record Predicate {ℓₗ ℓₒ} : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    ⦃ propositional ⦄ : Propositional{ℓₗ Lvl.⊔ ℓₒ}
    Domain : Type{ℓₒ}

  field
    ∀ₗ : (Domain → Stmt) → Stmt
    ∃ₗ : (Domain → Stmt) → Stmt

  field
    [∃]-intro : ∀{P : Domain → Stmt}{a} → P(a) → (∃ₗ P)
    [∃]-elim  : ∀{P : Domain → Stmt}{Z : Stmt} → (∀{x : Domain} → P(x) → Z) → (∃ₗ P) → Z

    [∀]-intro : ∀{P : Domain → Stmt} → (∀{x : Domain} → P(x)) → (∀ₗ P)
    [∀]-elim  : ∀{P : Domain → Stmt} → (∀ₗ P) → (∀{x : Domain} → P(x))
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
