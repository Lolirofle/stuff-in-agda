module Logic.Propositional where

open import Data
open import Functional
import      Level as Lvl
open import Relator.Equals(Lvl.𝟎)

record Syntax {lvl} (Stmt : Set(lvl)) (Formula : Set(lvl) → Set(lvl)) : Set(lvl) where
  field
    Prop : Stmt → Formula(Stmt)
    ⊤ : Formula(Stmt)
    ⊥ : Formula(Stmt)
    ¬_ : Formula(Stmt) → Formula(Stmt)
    _∧_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _∨_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇒_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    -- _⇐_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    -- _⇔_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    -- _⊕_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
open Syntax

-- Also known as Interpretation, Structure, Model
record Model {lvl} (Stmt : Set(lvl)) : Set(lvl) where
  field
    interpretStmt : Stmt → Bool

record Semantics {lvl} {Stmt : Set(lvl)} {Formula : Set(lvl) → Set(lvl)} (_⊧_ : Model(Stmt) → Formula(Stmt) → Set(lvl)) : Set(Lvl.𝐒(lvl)) where
  field
    {syn}     : Syntax Stmt Formula
    {metasyn} : Syntax (Set(lvl)) (const(Set(lvl)))

    [Prop]-satisfaction : ∀{𝔐 : Model(Stmt)}{stmt : Stmt} → (Model.interpretStmt 𝔐 stmt ≡ 𝑇) → (Prop metasyn (𝔐 ⊧ (Prop syn stmt)))
    [⊤]-satisfaction : ∀{𝔐 : Model(Stmt)} → Prop metasyn (𝔐 ⊧ (⊤ syn))
    [⊥]-satisfaction : ∀{𝔐 : Model(Stmt)} → ¬_ metasyn (Prop metasyn (𝔐 ⊧ (⊥ syn)))
    [¬]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ : Formula(Stmt)} → (¬_ metasyn (𝔐 ⊧ φ)) → (Prop metasyn (𝔐 ⊧ (¬_ syn φ)))
    [∧]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (_∧_ metasyn (𝔐 ⊧ φ₁) (𝔐 ⊧ φ₂)) → (Prop metasyn (𝔐 ⊧ (_∧_ syn φ₁ φ₂)))
    [∨]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (_∨_ metasyn (𝔐 ⊧ φ₁) (𝔐 ⊧ φ₂)) → (Prop metasyn (𝔐 ⊧ (_∨_ syn φ₁ φ₂)))
    [⇒]-satisfaction : ∀{𝔐 : Model(Stmt)}{φ₁ φ₂ : Formula(Stmt)} → (_∨_ metasyn (¬_ metasyn (𝔐 ⊧ φ₁)) (𝔐 ⊧ φ₂)) → (Prop metasyn (𝔐 ⊧ (_⇒_ syn φ₁ φ₂)))
