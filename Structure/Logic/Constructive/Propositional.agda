import      Lvl
open import Type

module Structure.Logic.Constructive.Propositional {ℓₗ} {Formula : Type{ℓₗ}} {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ}) where

open import Logic.Predicate

private variable X Y Z : Formula

-- Rules of bottom (falsity).
record Bottom(⊥ : Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    elim : Proof(⊥) → Proof(X)
⊥ = \ ⦃([∃]-intro ▫) : ∃(Bottom)⦄ → ▫
module ⊥ {▫} ⦃ p ⦄ = Bottom {▫} p

-- Rules of top (truth).
record Top(⊤ : Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro : Proof(⊤)
⊤ = \ ⦃([∃]-intro ▫) : ∃(Top)⦄ → ▫
module ⊤ {▫} ⦃ p ⦄ = Top {▫} p

-- Rules of conjunction (and).
record Conjunction(_∧_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro : Proof(X) → Proof(Y) → Proof(X ∧ Y)
    elimₗ : Proof(X ∧ Y) → Proof(X)
    elimᵣ : Proof(X ∧ Y) → Proof(Y)
_∧_ = \ ⦃([∃]-intro ▫) : ∃(Conjunction)⦄ → ▫
module ∧ {▫} ⦃ p ⦄ = Conjunction {▫} p

-- Rules of implication.
record Implication(_⟶_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro : (Proof(X) → Proof(Y)) → Proof(X ⟶ Y)
    elim  : Proof(X ⟶ Y) → Proof(X) → Proof(Y)
_⟶_ = \ ⦃([∃]-intro ▫) : ∃(Implication)⦄ → ▫
module ⟶ {▫} ⦃ p ⦄ = Implication {▫} p

-- Rules of reversed implication.
record Consequence(_⟵_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro : (Proof(X) → Proof(Y)) → Proof(Y ⟵ X)
    elim  : Proof(Y ⟵ X) → Proof(X) → Proof(Y)
_⟵_ = \ ⦃([∃]-intro ▫) : ∃(Consequence)⦄ → ▫
module ⟵ {▫} ⦃ p ⦄ = Consequence {▫} p

-- Rules of equivalence.
record Equivalence(_⟷_ : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro  : let _ = X in (Proof(Y) → Proof(X)) → (Proof(X) → Proof(Y)) → Proof(X ⟷ Y)
    elimₗ  : Proof(X ⟷ Y) → Proof(Y) → Proof(X)
    elimᵣ  : Proof(X ⟷ Y) → Proof(X) → Proof(Y)
_⟷_ = \ ⦃([∃]-intro ▫) : ∃(Equivalence)⦄ → ▫
module ⟷ {▫} ⦃ p ⦄ = Equivalence {▫} p

-- Rules of disjunction (or).
record Disjunction(_∨_  : Formula → Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    introₗ : Proof(X) → Proof(X ∨ Y)
    introᵣ : Proof(Y) → Proof(X ∨ Y)
    elim   : (Proof(X) → Proof(Z)) → (Proof(Y) → Proof(Z)) → Proof(X ∨ Y) → Proof(Z)
_∨_ = \ ⦃([∃]-intro ▫) : ∃(Disjunction)⦄ → ▫
module ∨ {▫} ⦃ p ⦄ = Disjunction {▫} p

-- Rules of negation (not).
record Negation(¬_ : Formula → Formula) : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    intro : (Proof(X) → Proof(Y)) → (Proof(X) → Proof(¬ Y)) → Proof(¬ X)
    elim  : Proof(X) → Proof(¬ X) → Proof(Y)
¬_ = \ ⦃([∃]-intro ▫) : ∃(Negation)⦄ → ▫
module ¬ {▫} ⦃ p ⦄ = Negation {▫} p

record Logic : Type{ℓₘₗ Lvl.⊔ ℓₗ} where
  field
    ⦃ bottom ⦄      : ∃(Bottom)
    ⦃ top ⦄         : ∃(Top)
    ⦃ conjunction ⦄ : ∃(Conjunction)
    ⦃ implication ⦄ : ∃(Implication)
    ⦃ consequence ⦄ : ∃(Consequence)
    ⦃ equivalence ⦄ : ∃(Equivalence)
    ⦃ disjunction ⦄ : ∃(Disjunction)
    ⦃ negation ⦄    : ∃(Negation)
