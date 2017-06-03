module Logic.Classic.Propositional.Syntax {ℓₚ} (Prop : Set(ℓₚ)) where

import Level as Lvl

infixl 1011 •_
infixl 1010 ¬_
infixl 1005 _∧_
infixl 1004 _∨_
infixl 1000 _⇐_ _⇔_ _⇒_

data Formula{ℓₜ} (T : Set(ℓₜ)) : Set(ℓₚ Lvl.⊔ ℓₜ) where
  •_ : Prop → Formula(T)

  ⊤ : Formula(T)
  ⊥ : Formula(T)

  ¬_ : Formula(T) → Formula(T)

  _∧_ : Formula(T) → Formula(T) → Formula(T)
  _∨_ : Formula(T) → Formula(T) → Formula(T)
  _⇒_ : Formula(T) → Formula(T) → Formula(T)

_⇐_ : ∀{ℓₜ}{T : Set(ℓₜ)} → Formula(T) → Formula(T) → Formula(T)
_⇐_ a b = _⇒_ b a

_⇔_ : ∀{ℓₜ}{T : Set(ℓₜ)} → Formula(T) → Formula(T) → Formula(T)
_⇔_ a b = (_⇐_ a b) ∧ (_⇒_ a b)
