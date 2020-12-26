module Metalogic.Constructive.NaturalDeduction.TreeModel{ℓₚ} (Proposition : Set(ℓₚ)) where

import Lvl

infixl 1011 •_
infixl 1010 ¬_
infixl 1005 _∧_
infixl 1004 _∨_
infixl 1000 _⇐_ _⇔_ _⇒_

data Formula : Set(ℓₚ) where
  •_ : Proposition → Formula

  ⊤ : Formula
  ⊥ : Formula

  ¬_ : Formula → Formula

  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  _⇒_ : Formula → Formula → Formula

_⇐_ : Formula → Formula → Formula
_⇐_ a b = _⇒_ b a

_⇔_ : Formula → Formula → Formula
_⇔_ a b = (_⇐_ a b) ∧ (_⇒_ a b)

{-# NO_POSITIVITY_CHECK #-}
data Tree : Formula → Set(ℓₚ) where
  [⊤]-intro : Tree(⊤)

  [⊥]-intro : ∀{φ} → Tree(φ) → Tree(¬ φ) → Tree(⊥)

  [¬]-intro : ∀{φ} → (Tree(φ) → Tree(⊥)) → Tree(¬ φ)
  [¬]-elim  : ∀{φ} → (Tree(¬ φ) → Tree(⊥)) → Tree(φ)

  [∧]-intro : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₂) → Tree(φ₁ ∧ φ₂)
  [∧]-elimₗ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₁)
  [∧]-elimᵣ  : ∀{φ₁ φ₂} → Tree(φ₁ ∧ φ₂) → Tree(φ₂)

  [∨]-introₗ : ∀{φ₁ φ₂} → Tree(φ₁) → Tree(φ₁ ∨ φ₂)
  [∨]-introᵣ : ∀{φ₁ φ₂} → Tree(φ₂) → Tree(φ₁ ∨ φ₂)
  [∨]-elim  : ∀{φ₁ φ₂ φ₃} → (Tree(φ₁) → Tree(φ₃)) → (Tree(φ₂) → Tree(φ₃)) → Tree(φ₁ ∨ φ₂) → Tree(φ₃)

  [⇒]-intro : ∀{φ₁ φ₂} → (Tree(φ₁) → Tree(φ₂)) → Tree(φ₁ ⇒ φ₂)
  [⇒]-elim  : ∀{φ₁ φ₂} → Tree(φ₁ ⇒ φ₂) → Tree(φ₁) → Tree(φ₂)

[⇐]-intro : ∀{φ₁ φ₂} → (Tree(φ₂) → Tree(φ₁)) → Tree(φ₁ ⇐ φ₂)
[⇐]-intro = [⇒]-intro

[⇐]-elim  : ∀{φ₁ φ₂} → Tree(φ₁ ⇐ φ₂) → Tree(φ₂) → Tree(φ₁)
[⇐]-elim = [⇒]-elim

[⇔]-intro  : ∀{φ₁ φ₂} → (Tree(φ₂) → Tree(φ₁)) → (Tree(φ₁) → Tree(φ₂)) → Tree(φ₁ ⇔ φ₂)
[⇔]-intro l r = [∧]-intro ([⇐]-intro l) ([⇒]-intro r)

[⇔]-elimₗ  : ∀{φ₁ φ₂} → Tree(φ₁ ⇔ φ₂) → Tree(φ₂) → Tree(φ₁)
[⇔]-elimₗ lr = [⇐]-elim([∧]-elimₗ(lr))

[⇔]-elimᵣ  : ∀{φ₁ φ₂} → Tree(φ₁ ⇔ φ₂) → Tree(φ₁) → Tree(φ₂)
[⇔]-elimᵣ lr = [⇒]-elim([∧]-elimᵣ(lr))
