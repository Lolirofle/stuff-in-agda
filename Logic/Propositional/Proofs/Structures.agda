module Logic.Propositional.Proofs.Structures where

import      Data.Tuple as Tuple
import      Lvl
open import Function
open import Functional
open import Logic
open import Logic.Propositional
import      Logic.Propositional.Theorems as Theorems
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

open import Structure.Relator
open import Structure.Function
open import Structure.Operator
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ {P : T → Type{ℓ}} where
  relator-function₁ : UnaryRelator(P) ↔ Function ⦃ equiv-B = [↔]-equiv ⦄ (P)
  UnaryRelator.substitution (Tuple.left  relator-function₁ (intro congruence))   xy = [↔]-to-[→] (congruence xy)
  Function.congruence       (Tuple.right relator-function₁ (intro substitution)) xy = [↔]-intro (substitution(symmetry(_≡_) xy)) (substitution xy)

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ {P : A → B → Type{ℓ}} where
  relator-function₂ : BinaryRelator(P) ↔ BinaryOperator ⦃ equiv-B = [↔]-equiv ⦄ (P)
  BinaryRelator.substitution (Tuple.left  relator-function₂ (intro congruence))   xy1 xy2 = [↔]-to-[→] (congruence xy1 xy2)
  BinaryOperator.congruence  (Tuple.right relator-function₂ (intro substitution)) xy1 xy2 = [↔]-intro (substitution(symmetry(_≡_) xy1) (symmetry(_≡_) xy2)) (substitution xy1 xy2)

{- TODO: Maybe a general Equiv and Transitivity for (_↔_) is possible with indexed relation structures? What I mean by indexed:
test : ∀{ℓ₁ ℓ₂}{T : TYPE ℓ₁}{ℓ : T → Lvl.Level} → ((x : T) → TYPE(ℓ x)) → TYPE ℓ₂

test2 : TYPE Lvl.𝟎
test2 = test{T = Lvl.Level}{ℓ = Lvl.𝐒} (\ℓ → TYPE ℓ)

instead of:

test : ∀{ℓ₁ ℓ₂}{T : TYPE ℓ₁}{ℓ : Lvl.Level} → TYPE ℓ → TYPE ℓ₂

Then all special cases for (_→_) and (_↔_) would finally be redundant. Also, substitution could be a special case of congruence, so *Relator would be special cases of *Operator
-}

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
