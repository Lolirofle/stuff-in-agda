module Structure.Set.Relators.Proofs where

open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.IntroInstances
import      Lvl
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Set.Relators hiding (_⊆_ ; _≡_)
open import Type

private variable ℓ ℓₗ ℓᵣ ℓₑ : Lvl.Level
private variable S Sₗ Sᵣ E : Type{ℓ}
private variable _∈_ : E → S → Stmt{ℓₗ}
private variable _⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣ}
private variable _≡_ : S → S → Stmt{ℓₑ}

module _ ⦃ eq : SetEqualityRelation(_∈_)(_∈_)(_≡_) ⦄ where
  [≡]-reflexivity : Reflexivity(_≡_)
  [≡]-reflexivity = intro([↔]-to-[←] [≡]-membership [↔]-reflexivity)

  [≡]-symmetry : Symmetry(_≡_)
  [≡]-symmetry = intro(\p → [↔]-to-[←] [≡]-membership ([↔]-symmetry ([↔]-to-[→] [≡]-membership p)))

  [≡]-transitivity : Transitivity(_≡_)
  [≡]-transitivity = intro(\p q → [↔]-to-[←] [≡]-membership ([↔]-transitivity ([↔]-to-[→] [≡]-membership p) ([↔]-to-[→] [≡]-membership q)))

  [≡]-equivalence : Equivalence(_≡_)
  [≡]-equivalence = intro ⦃ [≡]-reflexivity ⦄ ⦃ [≡]-symmetry ⦄ ⦃ [≡]-transitivity ⦄

module _ ⦃ sub : SubsetRelation(_∈_)(_∈_)(_⊆_) ⦄ where
  [⊆]-reflexivity : Reflexivity(_⊆_)
  [⊆]-reflexivity = intro([↔]-to-[←] [⊆]-membership [→]-reflexivity)

  [⊆]-transitivity : Transitivity(_⊆_)
  [⊆]-transitivity = intro(\p q → [↔]-to-[←] [⊆]-membership ([→]-transitivity ([↔]-to-[→] [⊆]-membership p) ([↔]-to-[→] [⊆]-membership q)))

module _
  ⦃ eq : SetEqualityRelation(_∈_)(_∈_)(_≡_) ⦄
  ⦃ sub : SubsetRelation(_∈_)(_∈_)(_⊆_) ⦄
  where

  [⊆][≡]-antisymmetry : Antisymmetry(_⊆_)(_≡_)
  [⊆][≡]-antisymmetry = intro(\p q → [↔]-to-[←] [≡]-membership ([↔]-intro ([↔]-to-[→] [⊆]-membership q) ([↔]-to-[→] [⊆]-membership p)))
