module Structure.Relator.Properties where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Type

module Names where
  module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
    ConversePattern : (T₁ → T₂ → Stmt{ℓ₃}) → (T₂ → T₁ → Stmt{ℓ₄}) → Stmt
    ConversePattern (_▫₁_) (_▫₂_) = (∀{x : T₁}{y : T₂} → (x ▫₁ y) → (y ▫₂ x))

  module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
    Symmetry : Stmt
    Symmetry = ConversePattern (_▫_) (_▫_)

    Asymmetry : Stmt
    Asymmetry = ConversePattern (_▫_) (x ↦ y ↦ ¬(x ▫ y))

    Reflexivity : Stmt
    Reflexivity = ∀{x : T} → (x ▫ x)

    Transitivity : Stmt
    Transitivity = ∀{x y z : T} → (x ▫ y) → (y ▫ z) → (x ▫ z)

    Irreflexivity : Stmt
    Irreflexivity = ∀{x : T} → ¬(x ▫ x)

    ConverseTotal : Stmt
    ConverseTotal = ∀{x y : T} → (x ▫ y) ∨ (y ▫ x)

    ConverseDichotomy : Stmt
    ConverseDichotomy = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

  module _ {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_▫₁_ : T → T → Stmt{ℓ₂}) (_▫₂_ : T → T → Stmt{ℓ₃}) where
    Antisymmetry : Stmt
    Antisymmetry = ∀{a b : T} → (a ▫₁ b) → (b ▫₁ a) → (a ▫₂ b)

  -- Trichotomy : {T : Type} → (T → T → Stmt) → Stmt
  -- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them

-- Definition of a reflexive binary relation
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Reflexivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Reflexivity(_▫_)
  reflexivity = inst-fn Reflexivity.proof

-- Definition of a transitive binary relation
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Transitivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Transitivity(_▫_)
  transitivity = inst-fn Transitivity.proof

-- The transitivity operator
infixl 1000 _🝖_
_🝖_ : ∀{ℓ}{T : Type{ℓ}}{_▫_ : T → T → Stmt{ℓ}} → ⦃ _ : Transitivity(_▫_) ⦄ → Names.Transitivity(_▫_)
_🝖_ {_}{T}{_▫_} = transitivity(_▫_)

-- Definition of a antisymmetric binary relation
module _ {ℓ₁}{ℓ₂}{ℓ₃} {T : Type{ℓ₁}} (_▫₁_ : T → T → Stmt{ℓ₂}) (_▫₂_ : T → T → Stmt{ℓ₃}) where
  record Antisymmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Antisymmetry(_▫₁_)(_▫₂_)
  antisymmetry = inst-fn Antisymmetry.proof

-- Definition of a irreflexive binary relation
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Irreflexivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Irreflexivity(_▫_)
  irreflexivity = inst-fn Irreflexivity.proof

-- Definition of a total binary relation.
-- Total in the sense that it, or its converse, holds.
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record ConverseTotal : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.ConverseTotal(_▫_)
  converseTotal = inst-fn ConverseTotal.proof

module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record ConverseDichotomy : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.ConverseDichotomy(_▫_)
  dichotomy = inst-fn ConverseDichotomy.proof

-- Trichotomy : {T : Type} → (T → T → Stmt) → Stmt
-- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them

-- Definition of a converse binary operation for a binary operation
-- record Converse {T₁ T₂ : Type} (_▫₁_ : T₁ → T₂ → Stmt) (_▫₂_ : T₂ → T₁ → Stmt) : Stmt where
--   constructor intro
-- 
--   field
--     converseₗ : Names.ConversePattern (_▫₂_) (_▫₁_)
--     converseᵣ : Names.ConversePattern (_▫₁_) (_▫₂_)
-- open Converse ⦃ ... ⦄ public
-- {x : T₁}{y : T₂} → (x ▫₁ y) ↔ (y ▫₂ x)

-- Definition of a symmetric binary operation
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Symmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Symmetry(_▫_)
  symmetry = inst-fn Symmetry.proof
-- {x y : T} → (x ▫ y) → (y ▫ x)

-- Definition of an asymmetric binary operation
module _ {ℓ₁}{ℓ₂} {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Asymmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Asymmetry(_▫_)
  asymmetry = inst-fn Asymmetry.proof
-- {x y : T} → (x ▫ y) → ¬(y ▫ x)
