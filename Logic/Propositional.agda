module Logic.Propositional where

open import Data
open import Functional
import      Level as Lvl
open import Relator.Equals(Lvl.𝟎)

record Syntax {lvl₁} {lvl₂} (Stmt : Set(lvl₁)) (Formula : Set(lvl₁) → Set(lvl₂)) : Set(lvl₁ Lvl.⊔ lvl₂) where
  field
    •_ : Stmt → Formula(Stmt)
    ⊤ : Formula(Stmt)
    ⊥ : Formula(Stmt)
    ¬_ : Formula(Stmt) → Formula(Stmt)
    _∧_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _∨_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇒_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇐_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇔_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⊕_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)

module Operators {lvl₁} {lvl₂} {Stmt : Set(lvl₁)} {Formula : Set(lvl₁) → Set(lvl₂)} (syn : Syntax Stmt Formula) where
  infixl 1011 •_
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_ _⊕_
  infixl 1000 _⇐_ _⇔_ _⇒_

  •_ = Syntax.•_ syn
  ⊤ = Syntax.⊤ syn
  ⊥ = Syntax.⊥ syn
  ¬_ = Syntax.¬_ syn
  _∧_ = Syntax._∧_ syn
  _∨_ = Syntax._∨_ syn
  _⇒_ = Syntax._⇒_ syn
  _⇐_ = Syntax._⇐_ syn
  _⇔_ = Syntax._⇔_ syn
  _⊕_ = Syntax._⊕_ syn

-- Also known as Interpretation, Structure, Model
record Model {lvl} (Stmt : Set(lvl)) : Set(lvl) where
  field
    interpretStmt : Stmt → Bool

-- TODO: Can this be called a "theory" of propositional logic? So that instances of the type Semantics is the "models" of logic?
record Semantics {lvl} {Stmt : Set(lvl)} {Formula : Set(lvl) → Set(lvl)} (_⊧_ : Model(Stmt) → Formula(Stmt) → Set(lvl)) : Set(Lvl.𝐒(lvl)) where
  field -- Definitions
    {syn}     : Syntax Stmt Formula
    {metasyn} : Syntax (Set(lvl)) (const(Set(lvl)))
  open Operators(syn)
  open Operators(metasyn)
    hiding (_⇒_)
    renaming (•_ to ◦_ ; _∧_ to _∧ₘ_ ; _∨_ to _∨ₘ_ ; ¬_ to ¬ₘ_ ; ⊤ to ⊤ₘ ; ⊥ to ⊥ₘ)
  field -- Axioms
    [•]-satisfaction : ∀{𝔐 : Model(Stmt)}{stmt : Stmt} → (Model.interpretStmt 𝔐 stmt ≡ 𝑇) → ◦(𝔐 ⊧ (• stmt))
    [⊤]-satisfaction : ∀{𝔐 : Model(Stmt)} → ◦(𝔐 ⊧ ⊤)
    [⊥]-satisfaction : ∀{𝔐 : Model(Stmt)} → ¬ₘ ◦(𝔐 ⊧ ⊥)
    [¬]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ : Formula(Stmt)} → (¬ₘ ◦(𝔐 ⊧ φ)) → ◦(𝔐 ⊧ (¬ φ))
    [∧]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (◦(𝔐 ⊧ φ₁) ∧ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∧ φ₂))
    [∨]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (◦(𝔐 ⊧ φ₁) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ∨ φ₂))
    [⇒]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → ((¬ₘ ◦(𝔐 ⊧ φ₁)) ∨ₘ ◦(𝔐 ⊧ φ₂)) → ◦(𝔐 ⊧ (φ₁ ⇒ φ₂))
-- TODO: How does the satisfaction definitions look like in constructive logic?
