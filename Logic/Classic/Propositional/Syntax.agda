module Logic.Classic.Propositional.Syntax {ℓ} (Prop : Set(ℓ)) where

infixl 1011 •_
infixl 1010 ¬_
infixl 1005 _∧_
infixl 1004 _∨_
infixl 1000 _⇐_ _⇔_ _⇒_

data Formula : Set(ℓ) where
  •_ : Prop → Formula

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
