module Logic.Propositional where

open import Data
open import Functional

module Syntax where
  infixl 1010 ¬_
  infixl 1005 _∧_
  infixl 1004 _∨_ _⊕_
  infixl 1000 _⇐_ _⇔_ _⇒_

  data Formula (Stmt : Set) : Set where
    -- Atoms
    Prop : Stmt → Formula(Stmt) -- A proposition
    ⊤ : Formula(Stmt)
    ⊥ : Formula(Stmt)

    -- Unary operators
    ¬_ : Formula(Stmt) → Formula(Stmt)

    -- Binary operators
    _∧_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _∨_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇒_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇐_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⇔_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)
    _⊕_ : Formula(Stmt) → Formula(Stmt) → Formula(Stmt)

  -- Could also be seen as some kind of "map" function
  -- This is sometimes written as φ[A/B] or something similar for a formula φ with substitution of A to B
  substitute : ∀{Stmt₁ Stmt₂} → (Stmt₁ → Stmt₂) → Formula(Stmt₁) → Formula(Stmt₂)
  substitute f (Prop p) = Prop(f(p))
  substitute _ ⊤ = ⊤
  substitute _ ⊥ = ⊥
  substitute f (¬ φ) = ¬ (substitute f φ)
  substitute f (φ₁ ∧ φ₂) = (substitute f φ₁) ∧ (substitute f φ₂)
  substitute f (φ₁ ∨ φ₂) = (substitute f φ₁) ∨ (substitute f φ₂)
  substitute f (φ₁ ⇒ φ₂) = (substitute f φ₁) ⇒ (substitute f φ₂)
  substitute f (φ₁ ⇐ φ₂) = (substitute f φ₁) ⇐ (substitute f φ₂)
  substitute f (φ₁ ⇔ φ₂) = (substitute f φ₁) ⇔ (substitute f φ₂)
  substitute f (φ₁ ⊕ φ₂) = (substitute f φ₁) ⊕ (substitute f φ₂)

module Semantics where
  -- Also known as Interpretation, Structure, Model
  record Model (Stmt : Set) : Set where
    field
      interpretStmt : Stmt → Bool

  interpret : ∀{Stmt} → Model(Stmt) → Formula(Stmt) → Bool
  interpret 𝔐 φ = substitute (interpretStmt 𝔐) φ

  _⊧_ : Model → Formula → Set
  𝔐 ⊧ φ = (interpret 𝔐 φ) ≡ 𝑇

  record Logic (Formula : Set → Set) (_⊨_ : Formula → Formula) : Set where
    field
      -- Symbols
      ⊤ : Formula
      ⊥ : Formula
      ¬_ : Formula → Formula
      _∧_ : Formula → Formula → Formula
      _∨_ : Formula → Formula → Formula
      _⇒_ : Formula → Formula → Formula
      _⇐_ : Formula → Formula → Formula
      _⇔_ : Formula → Formula → Formula
      _⊕_ : Formula → Formula → Formula

      -- Axioms
      [⊤]-satisfaction : ∀{𝔐 : Model} → (𝔐 ⊧ ⊤)
