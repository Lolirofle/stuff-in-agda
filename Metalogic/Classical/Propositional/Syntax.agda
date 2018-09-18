module Metalogic.Classical.Propositional.Syntax {ℓₚ} (Proposition : Set(ℓₚ)) where

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
