module Structure.Set.Operators.Proofs.LogicalOperator where

open import Functional using (_$_)
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.IntroInstances
import      Lvl
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Set.Equiv
open import Structure.Set.Operators
open import Structure.Set.Relators using (SetEqualityRelation ; [≡]-membership)
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)
open import Syntax.Implication
open import Type

private variable ℓ ℓₗ ℓₗ₁ ℓₗ₂ ℓᵣ ℓᵣₑₗ ℓₒ ℓₛ ℓₑ : Lvl.Level
private variable A B C S S₁ S₂ Sₒ Sᵢ Sₗ Sᵣ E E₁ E₂ Eₗ Eᵣ I O : Type{ℓ}
private variable _∈_ _∈ₒ_ _∈ᵢ_ : E → S → Stmt{ℓₗ}
private variable _∈ₗ_ : E → Sₗ → Stmt{ℓₗ}
private variable _∈ᵣ_ : E → Sᵣ → Stmt{ℓᵣ}
private variable _⊆_ : Sₗ → Sᵣ → Stmt{ℓᵣ}
private variable _≡_ : S → S → Stmt{ℓₑ}
private variable _△_ _△₁_ _△₂_ : Stmt{ℓₗ} → Stmt{ℓᵣ} → Stmt{ℓ}
private variable _▫_ _▫₁_ _▫₂_ : Sₗ → Sᵣ → Sₒ
private variable idₗ idₛ : S

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△_)(_▫_) ⦄
  ⦃ binOp : BinaryOperator(_△_) ⦄
  where

  logicalOperator-operator : BinaryOperator(_▫_)
  logicalOperator-operator = intro \p q → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op   ⇔
    congruence₂(_△_)
      ([↔]-to-[→] [≡]-membership p)
      ([↔]-to-[→] [≡]-membership q) ⇔-sym
    LogicalOperator.membership op

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈ₒ_)(equiv) ⦄
  ⦃ op : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈ₒ_) (_△_)(_▫_) ⦄
  ⦃ comm : Commutativity(_△_) ⦄
  where

  logicalOperator-commutativity : Commutativity(_▫_)
  logicalOperator-commutativity = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op ⇔
    commutativity(_△_)            ⇔-sym
    LogicalOperator.membership op

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△_)(_▫_) ⦄
  ⦃ binOp : BinaryOperator(_△_) ⦄
  ⦃ assoc : Associativity(_△_) ⦄
  where

  logicalOperator-associativity : Associativity(_▫_)
  logicalOperator-associativity = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op                        ⇔
    congruence₂-₁(_△_) _ (LogicalOperator.membership op) ⇔
    associativity(_△_)                                   ⇔-sym
    congruence₂-₂(_△_) _ (LogicalOperator.membership op) ⇔-sym
    LogicalOperator.membership op

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△_)(_▫_) ⦄
  ⦃ binOp : BinaryOperator(_△_) ⦄
  ⦃ ident : Identityₗ(_△_)(idₗ) ⦄
  (ident-eq : ∀{x} → (x ∈ idₛ) ↔ idₗ)
  where

  logicalOperator-identityₗ : Identityₗ(_▫_)(idₛ)
  logicalOperator-identityₗ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op ⇔
    congruence₂-₁(_△_) _ ident-eq ⇔
    identityₗ(_△_)(idₗ)

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△_)(_▫_) ⦄
  ⦃ binOp : BinaryOperator(_△_) ⦄
  ⦃ ident : Identityᵣ(_△_)(idₗ) ⦄
  (ident-eq : ∀{x} → (x ∈ idₛ) ↔ idₗ)
  where

  logicalOperator-identityᵣ : Identityᵣ(_▫_)(idₛ)
  logicalOperator-identityᵣ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op ⇔
    congruence₂-₂(_△_) _ ident-eq ⇔
    identityᵣ(_△_)(idₗ)

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op₁ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₁_)(_▫₁_) ⦄
  ⦃ op₂ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₂_)(_▫₂_) ⦄
  ⦃ binOp₁ : BinaryOperator(_△₁_) ⦄
  ⦃ absorp : Absorptionₗ(_△₁_)(_△₂_) ⦄
  where

  logicalOperator-absorptionₗ : Absorptionₗ(_▫₁_)(_▫₂_)
  logicalOperator-absorptionₗ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op₁                         ⇔
    congruence₂-₂(_△₁_) _ (LogicalOperator.membership op₂) ⇔
    absorptionₗ(_△₁_)(_△₂_)

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op₁ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₁_)(_▫₁_) ⦄
  ⦃ op₂ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₂_)(_▫₂_) ⦄
  ⦃ binOp₁ : BinaryOperator(_△₁_) ⦄
  ⦃ absorp : Absorptionᵣ(_△₁_)(_△₂_) ⦄
  where

  logicalOperator-absorptionᵣ : Absorptionᵣ(_▫₁_)(_▫₂_)
  logicalOperator-absorptionᵣ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op₁                         ⇔
    congruence₂-₁(_△₁_) _ (LogicalOperator.membership op₂) ⇔
    absorptionᵣ(_△₁_)(_△₂_)

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op₁ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₁_)(_▫₁_) ⦄
  ⦃ op₂ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₂_)(_▫₂_) ⦄
  ⦃ binOp₁ : BinaryOperator(_△₁_) ⦄
  ⦃ binOp₂ : BinaryOperator(_△₂_) ⦄
  ⦃ distri : Distributivityₗ(_△₁_)(_△₂_) ⦄
  where

  logicalOperator-distributivityₗ : Distributivityₗ(_▫₁_)(_▫₂_)
  logicalOperator-distributivityₗ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op₁                         ⇔
    congruence₂-₂(_△₁_) _ (LogicalOperator.membership op₂) ⇔
    distributivityₗ(_△₁_)(_△₂_)                            ⇔-sym
    congruence₂(_△₂_)
      (LogicalOperator.membership op₁)
      (LogicalOperator.membership op₁)                     ⇔-sym
    LogicalOperator.membership op₂

module _
  ⦃ equiv : Equiv{ℓₑ}(S) ⦄
  ⦃ ext : SetExtensionality(_∈_)(equiv) ⦄
  ⦃ op₁ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₁_)(_▫₁_) ⦄
  ⦃ op₂ : LogicalOperator{Sₗ = S} (_∈_)(_∈_)(_∈_) (_△₂_)(_▫₂_) ⦄
  ⦃ binOp₁ : BinaryOperator(_△₁_) ⦄
  ⦃ binOp₂ : BinaryOperator(_△₂_) ⦄
  ⦃ distri : Distributivityᵣ(_△₁_)(_△₂_) ⦄
  where

  logicalOperator-distributivityᵣ : Distributivityᵣ(_▫₁_)(_▫₂_)
  logicalOperator-distributivityᵣ = intro \{_} → [↔]-to-[←] [≡]-membership $
    LogicalOperator.membership op₁                         ⇔
    congruence₂-₁(_△₁_) _ (LogicalOperator.membership op₂) ⇔
    distributivityᵣ(_△₁_)(_△₂_)                            ⇔-sym
    congruence₂(_△₂_)
      (LogicalOperator.membership op₁)
      (LogicalOperator.membership op₁)                     ⇔-sym
    LogicalOperator.membership op₂

-- TODO: Lattice, SetAlgebra
