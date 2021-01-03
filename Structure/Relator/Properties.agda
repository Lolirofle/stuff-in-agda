module Structure.Relator.Properties where

open import Functional
import      Lvl
open import Lang.Instance
open import Logic
import      Structure.Relator.Names as Names
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable T A B C D E : Type{ℓ}

-- Definition of a reflexive binary relation
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Reflexivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Reflexivity(_▫_)
  reflexivity = inst-fn Reflexivity.proof

-- Definition of a transitive binary relation
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Transitivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Transitivity(_▫_)
  transitivity = inst-fn Transitivity.proof

-- Definition of a antisymmetric binary relation
module _ {T : Type{ℓ₁}} (_▫₁_ : T → T → Stmt{ℓ₂}) (_▫₂_ : T → T → Stmt{ℓ₃}) where
  record Antisymmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.Antisymmetry(_▫₁_)(_▫₂_)
  antisymmetry = inst-fn Antisymmetry.proof

-- Definition of a irreflexive binary relation
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Irreflexivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Irreflexivity(_▫_)
  irreflexivity = inst-fn Irreflexivity.proof

-- Definition of a total binary relation.
-- Total in the sense that it, or its converse, holds.
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record ConverseTotal : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.ConverseTotal(_▫_)
  converseTotal = inst-fn ConverseTotal.proof

-- Definition of a converse dichotomy.
-- It or its converse always holds, but never both at the same time.
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record ConverseDichotomy : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.ConverseDichotomy(_▫_)
  dichotomy = inst-fn ConverseDichotomy.proof

module _ {T : Type{ℓ₁}} (_▫₁_ : T → T → Stmt{ℓ₂}) (_▫₂_ : T → T → Stmt{ℓ₃}) where
  record ConverseTrichotomy : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field proof : Names.ConverseTrichotomy(_▫₁_)(_▫₂_)
  trichotomy = inst-fn ConverseTrichotomy.proof

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
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Symmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Symmetry(_▫_)
  symmetry = inst-fn Symmetry.proof
-- {x y : T} → (x ▫ y) → (y ▫ x)

-- Definition of an asymmetric binary operation
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record Asymmetry : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Asymmetry(_▫_)
  asymmetry = inst-fn Asymmetry.proof
-- {x y : T} → (x ▫ y) → ¬(y ▫ x)

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : A → B → Stmt{ℓ₂}) where
  record _⊆₂_ : Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Subrelation(_▫₁_)(_▫₂_)
  sub₂ = inst-fn _⊆₂_.proof

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : A → B → Stmt{ℓ₂}) where
  _⊇₂_ = (_▫₂_) ⊆₂ (_▫₁_)
  module _⊇₂_ inst = _⊆₂_ {_▫₁_ = _▫₂_}{_▫₂_ = _▫₁_} inst
  super₂ = inst-fn _⊇₂_.proof

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : A → A → Stmt{ℓ₂}) where
  record Subtransitivityₗ : Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Subtransitivityₗ(_▫₁_)(_▫₂_)
  subtransitivityₗ = inst-fn Subtransitivityₗ.proof

module _ (_▫₁_ : A → B → Stmt{ℓ₁}) (_▫₂_ : B → B → Stmt{ℓ₂}) where
  record Subtransitivityᵣ : Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.Subtransitivityᵣ(_▫₁_)(_▫₂_)
  subtransitivityᵣ = inst-fn Subtransitivityᵣ.proof

-- Definition of a cotransitive binary relation
module _ {T : Type{ℓ₁}} (_▫_ : T → T → Stmt{ℓ₂}) where
  record CoTransitivity : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : Names.CoTransitivity(_▫_)
  cotransitivity = inst-fn CoTransitivity.proof
