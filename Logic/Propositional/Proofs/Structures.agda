module Logic.Propositional.Proofs.Structures where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
import      Logic.Propositional.Theorems as Theorems
open import Structure.Operator.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl

private variable ℓ : Lvl.Level

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
  [↔]-reflexivity : Reflexivity{ℓ₂ = ℓ}(_↔_)
  [↔]-reflexivity = intro Theorems.[↔]-reflexivity

instance
  [↔]-symmetry : Symmetry{ℓ₂ = ℓ}(_↔_)
  [↔]-symmetry = intro Theorems.[↔]-symmetry

instance
  [↔]-transitivity : Transitivity{ℓ₂ = ℓ}(_↔_)
  [↔]-transitivity = intro Theorems.[↔]-transitivity

instance
  [↔]-antisymmetry : Antisymmetry{ℓ₂ = ℓ}(_→ᶠ_)(_↔_)
  [↔]-antisymmetry = intro(swap [↔]-intro)

instance
  [↔]-equivalence : Equivalence{ℓ₂ = ℓ}(_↔_)
  [↔]-equivalence = intro

-- TODO: Move this to its own file
instance
  [↔]-equiv : Equiv(Stmt{ℓ})
  [↔]-equiv = intro(_↔_) ⦃ [↔]-equivalence ⦄

instance
  [∧]-symmetry : Symmetry{ℓ₂ = ℓ}(_∧_)
  [∧]-symmetry = intro Theorems.[∧]-symmetry

instance
  [∨]-symmetry : Symmetry{ℓ₂ = ℓ}(_∨_)
  [∨]-symmetry = intro Theorems.[∨]-symmetry

instance
  [∧][↔]-sub : (_∧_) ⊆₂ (_↔_ {ℓ})
  [∧][↔]-sub = intro Theorems.[∧]-to-[↔]

instance
  [∧][→]-sub : (_∧_) ⊆₂ (_→ᶠ_ {ℓ})
  [∧][→]-sub = intro Theorems.[∧]-to-[→]

instance
  [∧][←]-sub : (_∧_) ⊆₂ (_←_ {ℓ})
  [∧][←]-sub = intro Theorems.[∧]-to-[←]

instance
  [∧][∨]-sub : (_∧_) ⊆₂ (_∨_ {ℓ})
  [∧][∨]-sub = intro Theorems.[∧]-to-[∨]

-- TODO: Fix Structure.Setoid.WithLvl in Structure.Operator.Properties
-- instance
--   [∧]-associativity : Associativity ⦃ [↔]-equiv ⦄ (_∧_)
