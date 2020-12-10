module Sets.IterativeSet where

import      Lvl
open import Logic
open import Type

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level

  -- A model of constructive set theory (CZF) by using W-types (iterative sets).
  -- The interpretation of Iset being a type of sets comes from the idea that the image of `elem` is a set of elements.
  record Iset : Type{Lvl.𝐒(ℓ)} where
    constructor set
    inductive
    pattern
    field
      {Index} : Type{ℓ}
      elem : Index → Iset{ℓ}
  open Iset

  Iset-index-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{A : Iset{ℓ₁}} → (∀{i : Index(A)} → P(elem(A)(i))) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  Iset-index-induction {P = P} proof {set elem} = proof{_} \{i} → Iset-index-induction{P = P} proof {elem(i)}
