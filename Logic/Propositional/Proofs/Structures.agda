module Logic.Propositional.Proofs.Structures where

import      Data.Tuple as Tuple
import      Lvl
open import Function
open import Functional
open import Logic
open import Logic.Propositional
import      Logic.Propositional.Theorems as Theorems
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

open import Logic.Propositional.Equiv public

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}

instance
  [→]-reflexivity : Reflexivity{ℓ₂ = ℓ}(_→ᶠ_)
  [→]-reflexivity = intro Theorems.[→]-reflexivity

instance
  [→]-transitivity : Transitivity{ℓ₂ = ℓ}(_→ᶠ_)
  [→]-transitivity = intro Theorems.[→]-transitivity

module _ where
  [←]-reflexivity : Reflexivity{ℓ₂ = ℓ}(_←_)
  [←]-reflexivity = intro Theorems.[→]-reflexivity

module _ where
  [←]-transitivity : Transitivity{ℓ₂ = ℓ}(_←_)
  [←]-transitivity = intro (swap Theorems.[→]-transitivity)

instance
  [↔]-antisymmetry : Antisymmetry{ℓ₂ = ℓ}(_→ᶠ_)(_↔_)
  [↔]-antisymmetry = intro(swap [↔]-intro)

instance
  [∧]-symmetry : Symmetry{ℓ₂ = ℓ}(_∧_)
  [∧]-symmetry = intro Theorems.[∧]-symmetry

instance
  [∨]-symmetry : Symmetry{ℓ₂ = ℓ}(_∨_)
  [∨]-symmetry = intro Theorems.[∨]-symmetry

instance
  [∧][↔]-sub : (_∧_) ⊆₂ (_↔_ {ℓ₁}{ℓ₂})
  [∧][↔]-sub = intro Theorems.[∧]-to-[↔]

instance
  [∧][→]-sub : (_∧_) ⊆₂ (_→ᶠ_ {ℓ₁}{ℓ₂})
  [∧][→]-sub = intro Theorems.[∧]-to-[→]

instance
  [∧][←]-sub : (_∧_) ⊆₂ (_←_ {ℓ₁}{ℓ₂})
  [∧][←]-sub = intro Theorems.[∧]-to-[←]

instance
  [∧][∨]-sub : (_∧_) ⊆₂ (_∨_ {ℓ₁}{ℓ₂})
  [∧][∨]-sub = intro Theorems.[∧]-to-[∨]

instance
  [∧]-associativity : Associativity ⦃ [↔]-equiv ⦄ (_∧_ {ℓ})
  [∧]-associativity = intro Theorems.[∧]-associativity

instance
  [∧]-operator : BinaryOperator ⦃ [↔]-equiv{ℓ₁} ⦄ ⦃ [↔]-equiv{ℓ₂} ⦄ ⦃ [↔]-equiv ⦄ (_∧_)
  BinaryOperator.congruence [∧]-operator = Theorems.[∧]-map-[↔]

instance
  [∨]-operator : BinaryOperator ⦃ [↔]-equiv{ℓ₁} ⦄ ⦃ [↔]-equiv{ℓ₂} ⦄ ⦃ [↔]-equiv ⦄ (_∨_)
  BinaryOperator.congruence [∨]-operator = Theorems.[∨]-map-[↔]

instance
  [→]-operator : BinaryOperator ⦃ [↔]-equiv{ℓ₁} ⦄ ⦃ [↔]-equiv{ℓ₂} ⦄ ⦃ [↔]-equiv ⦄ (_→ᶠ_)
  BinaryOperator.congruence [→]-operator = Theorems.[→]-map-[↔]

instance
  [↔]-operator : BinaryOperator ⦃ [↔]-equiv{ℓ₁} ⦄ ⦃ [↔]-equiv{ℓ₂} ⦄ ⦃ [↔]-equiv ⦄ (_↔_)
  BinaryOperator.congruence [↔]-operator = Theorems.[↔]-map-[↔]
