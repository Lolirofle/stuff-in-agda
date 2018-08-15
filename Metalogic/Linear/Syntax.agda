module Metalogic.Linear.Syntax {ℓₚ} (Prop : Set(ℓₚ)) where

import Lvl

-- https://en.wikipedia.org/wiki/Linear_logic
-- https://plato.stanford.edu/entries/logic-linear/#ProSys

data Formula : Set(ℓₚ) where
  •_ : Prop → Formula

  -- Top
  ⊤ : Formula

  -- Bottom
  ⊥ : Formula



  -- Classical conjunction
  _∧_ : Formula → Formula → Formula

  -- Classical disjunction
  _∨_ : Formula → Formula → Formula



  -- Additive and
  _&_ : Formula → Formula → Formula

  -- Additive or
  _⊕_ : Formula → Formula → Formula



  -- Multiplicative and
  _⊗_ : Formula → Formula → Formula

  -- Multiplicative or
  _⅋_ : Formula → Formula → Formula



  -- Linear implication
  _⊸_ : Formula → Formula → Formula
