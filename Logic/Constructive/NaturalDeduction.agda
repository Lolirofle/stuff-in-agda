module Logic.Constructive.NaturalDeduction where

open import Functional
import      Lvl
open import Type

module Propositional {ℓ} (Stmt : Type{ℓ}) where
  record Proposition : Type{Lvl.𝐒(ℓ)} where
    infixl 10000 •_

    field
      •_ : Stmt → Type{ℓ}

  record Bottom ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    field
      ⊥    : Stmt

    field
      intro : ∀{X} → •(X) → (•(X) → •(⊥)) → •(⊥)
      elim  : ∀{X} → •(⊥) → •(X)

  record Top ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    field
      ⊤    : Stmt

    field
      intro : •(⊤)

  record Conjunction ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    infixl 1005 _∧_

    field
      _∧_  : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → •(X) → •(Y) → •(X ∧ Y)
      elimₗ  : ∀{X Y} → •(X ∧ Y) → •(X)
      elimᵣ  : ∀{X Y} → •(X ∧ Y) → •(Y)

  record Implication ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    infixl 1000 _⟶_

    field
      _⟶_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → •(Y) → •(X ⟶ Y)
      elim  : ∀{X Y} → •(X ⟶ Y) → •(X) → •(Y)

  record ReversedImplication ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    infixl 1000 _⟵_

    field
      _⟵_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → •(Y) → •(Y ⟵ X)
      elim  : ∀{X Y} → •(Y ⟵ X) → •(X) → •(Y)

  record Equivalence ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    infixl 1000 _⟷_

    field
      _⟷_ : Stmt → Stmt → Stmt

    field
      intro : ∀{X Y} → (•(X) ← •(Y)) → (•(X) → •(Y)) → •(X ⟷ Y)
      elimₗ  : ∀{X Y} → •(X ⟷ Y) → •(Y) → •(X)
      elimᵣ  : ∀{X Y} → •(X ⟷ Y) → •(X) → •(Y)

  record Disjunction ⦃ _ : Proposition ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public

    infixl 1004 _∨_

    field
      _∨_  : Stmt → Stmt → Stmt

    field
      introₗ : ∀{X Y} → •(X) → •(X ∨ Y)
      introᵣ : ∀{X Y} → •(Y) → •(X ∨ Y)
      elim  : ∀{X Y Z} → •(X ∨ Y) → (•(X) → •(Z)) → (•(Y) → •(Z)) → •(Z)

  record Negation ⦃ _ : Proposition ⦄ ⦃ _ : Bottom ⦄ : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public
    open Bottom      ⦃ ... ⦄ hiding (•_) public

    infixl 1010 ¬_

    field
      ¬_   : Stmt → Stmt

    field
      intro : ∀{X} → (•(X) → •(⊥)) → •(¬ X)
      elim  : ∀{X} → •(¬ X) → •(X) → •(⊥)

  -- A theory of constructive propositional logic expressed using natural deduction rules
  record Theory : Type{Lvl.𝐒(ℓ)} where
    open Proposition ⦃ ... ⦄ public
    open Conjunction ⦃ ... ⦄ hiding (•_) renaming (intro to [∧]-intro ; elimₗ to [∧]-elimₗ ; elimᵣ to [∧]-elimᵣ) public
    open Disjunction ⦃ ... ⦄ hiding (•_) renaming (introₗ to [∨]-introₗ ; introᵣ to [∨]-introᵣ ; elim to [∨]-elim) public
    open Implication ⦃ ... ⦄ hiding (•_) renaming (intro to [→]-intro ; elim to [→]-elim) public
    open Equivalence ⦃ ... ⦄ hiding (•_) renaming (intro to [↔]-intro ; elimₗ to [↔]-elimₗ ; elimᵣ to [↔]-elimᵣ) public
    open Negation    ⦃ ... ⦄ hiding (•_) renaming (intro to [¬]-intro ; elim to [¬]-elim) public
    open Bottom      ⦃ ... ⦄ hiding (•_) renaming (intro to [⊥]-intro ; elim to [⊥]-elim) public
    open Top         ⦃ ... ⦄ hiding (•_) renaming (intro to [⊤]-intro) public

    field
      ⦃ proposition ⦄ : Proposition
      ⦃ bottom ⦄      : Bottom
      ⦃ top ⦄         : Top
      ⦃ conjunction ⦄ : Conjunction
      ⦃ disjunction ⦄ : Disjunction
      ⦃ implication ⦄ : Implication
      ⦃ equivalence ⦄ : Equivalence
      ⦃ negation ⦄    : Negation

module Predicate {ℓₗ ℓₒ} (Obj : Type{ℓₒ}) (Stmt : Type{ℓₗ Lvl.⊔ ℓₒ}) ⦃ _ : Propositional.Proposition(Stmt) ⦄ where
  open Propositional(Stmt) renaming (Theory to PropositionalTheory)
  open Proposition ⦃ ... ⦄

  record Object : Type{Lvl.𝐒(ℓₒ)} where
    field
      obj : Obj → Type{ℓₒ}

  record UniversalQuantification : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
    field
      ∀ₗ : (Obj → Stmt) → Stmt

    field
      intro : ∀{P : Obj → Stmt} → (∀{x : Obj} → •(P(x))) → •(∀ₗ P)
      elim  : ∀{P : Obj → Stmt} → •(∀ₗ P) → (∀{x : Obj} → •(P(x)))

  record ExistentialQuantification : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
    field
      ∃ₗ : (Obj → Stmt) → Stmt

    field
      intro : ∀{P : Obj → Stmt}{a} → •(P(a)) → •(∃ₗ P)
      elim  : ∀{P : Obj → Stmt}{Z : Stmt} → (∀{x : Obj} → •(P(x)) → •(Z)) → •(∃ₗ P) → •(Z)

  -- A theory of constructive predicate/(first-order) logic expressed using natural deduction rules
  record Theory  : Type{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
    open Propositional.Theory      ⦃ ... ⦄ public
    open UniversalQuantification   ⦃ ... ⦄ renaming (intro to [∀]-intro ; elim to [∀]-elim) public
    open ExistentialQuantification ⦃ ... ⦄ renaming (intro to [∃]-intro ; elim to [∃]-elim) public

    field
      ⦃ propositional ⦄             : PropositionalTheory
      ⦃ universalQuantification ⦄   : UniversalQuantification
      ⦃ existentialQuantification ⦄ : ExistentialQuantification
