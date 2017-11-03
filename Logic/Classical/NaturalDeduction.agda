module Logic.Classical.NaturalDeduction where

open import Functional
import      Lvl
open import Type

-- TODO: Maybe it is worth to try and take a more minimal approach? (Less axioms? Is this more practical/impractical?)

-- Theory of classical propositional logic expressed using natural deduction rules
record Propositional {ℓ} (Stmt : Type{ℓ}) : Type{Lvl.𝐒(ℓ)} where
  infixl 10000 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_
  infixl 1000 _⟵_ _⟷_ _⟶_

  field
    •_ : Stmt → Type{ℓ}

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
    [∧]-intro : ∀{X Y} → •(X) → •(Y) → •(X ∧ Y)
    [∧]-elimₗ  : ∀{X Y} → •(X ∧ Y) → •(X)
    [∧]-elimᵣ  : ∀{X Y} → •(X ∧ Y) → •(Y)

    [→]-intro : ∀{X Y} → •(Y) → •(X ⟶ Y)
    [→]-elim  : ∀{X Y} → •(X) → •(X ⟶ Y) → •(Y)

    [←]-intro : ∀{X Y} → •(Y) → •(Y ⟵ X)
    [←]-elim  : ∀{X Y} → •(X) → •(Y ⟵ X) → •(Y)

    [↔]-intro : ∀{X Y} → (•(X) ← •(Y)) → (•(X) → •(Y)) → •(X ⟷ Y)
    [↔]-elimₗ  : ∀{X Y} → •(X ⟷ Y) → •(X ⟵ Y)
    [↔]-elimᵣ  : ∀{X Y} → •(X ⟷ Y) → •(X ⟶ Y)

    [∨]-introₗ : ∀{X Y} → •(X) → •(X ∨ Y)
    [∨]-introᵣ : ∀{X Y} → •(Y) → •(X ∨ Y)
    [∨]-elim  : ∀{X Y Z} → (•(X) → •(Z)) → (•(Y) → •(Z)) → •(X ∨ Y) → •(Z)

    [¬]-intro : ∀{X} → (•(X) → •(⊥)) → •(¬ X)
    [¬]-elim  : ∀{X} → (•(¬ X) → •(⊥)) → •(X)

    [⊥]-intro : ∀{X} → •(X) → (•(X) → •(⊥)) → •(⊥)
    [⊥]-elim  : ∀{X} → •(⊥) → •(X)

    [⊤]-intro : •(⊤)
open Propositional ⦃ ... ⦄ public

-- Theory of classical predicate/(first-order) logic expressed using natural deduction rules
record Predicate {ℓₗ ℓₒ} (Stmt : Type{ℓₗ Lvl.⊔ ℓₒ}) : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    ⦃ propositional ⦄ : Propositional{ℓₗ Lvl.⊔ ℓₒ}(Stmt)

  field
    ∀ₗ : ∀{X : Type{ℓₒ}} → (X → Stmt) → Stmt
    ∃ₗ : ∀{X : Type{ℓₒ}} → (X → Stmt) → Stmt

  field
    [∃]-intro : ∀{X}{P : X → Stmt}{a} → •(P(a)) → •(∃ₗ P)
    [∃]-elim  : ∀{X}{P : X → Stmt}{Z : Stmt} → (∀{x : X} → •(P(x)) → •(Z)) → •(∃ₗ P) → •(Z)

    [∀]-intro : ∀{X}{P : X → Stmt} → (∀{x : X} → •(P(x))) → •(∀ₗ P)
    [∀]-elim  : ∀{X}{P : X → Stmt} → •(∀ₗ P) → (∀{x : X} → •(P(x)))
open Predicate ⦃ ... ⦄ public
