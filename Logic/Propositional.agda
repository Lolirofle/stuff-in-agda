module Logic.Propositional where

import      BidirectionalFunction
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Function
open import Functional
open import Logic
import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

infixl 1010 ¬_ ¬¬_
infixl 1005 _∧_
infixl 1004 _∨_

------------------------------------------
-- Conjunction (AND)

_∧_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_∧_ = _⨯_

pattern [∧]-intro p q = p , q

[∧]-elimₗ : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ∧ Q) → P
[∧]-elimₗ = Tuple.left

[∧]-elimᵣ : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ∧ Q) → Q
[∧]-elimᵣ = Tuple.right

[∧]-map = Tuple.map

------------------------------------------
-- Implication

[→]-elim : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (P → Q) → Q
[→]-elim = apply

[→]-intro : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P → Q) → (P → Q)
[→]-intro = _$_

------------------------------------------
-- Reverse implication

open Function using (_←_) public

[←]-intro : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P → Q) → (Q ← P)
[←]-intro = [→]-intro

[←]-elim : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (Q ← P) → Q
[←]-elim = [→]-elim

------------------------------------------
-- Equivalence

open BidirectionalFunction using (_↔_) public
pattern [↔]-intro l r = l , r

[↔]-elimₗ : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → Q → (P ↔ Q) → P
[↔]-elimₗ = swap BidirectionalFunction._$ₗ_

[↔]-elimᵣ : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (P ↔ Q) → Q
[↔]-elimᵣ = swap BidirectionalFunction._$ᵣ_

[↔]-to-[←] : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ↔ Q) → (Q → P)
[↔]-to-[←] = BidirectionalFunction._$ₗ_

[↔]-to-[→] : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ↔ Q) → (P → Q)
[↔]-to-[→] = BidirectionalFunction._$ᵣ_

------------------------------------------
-- Disjunction (OR)

_∨_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_∨_ = _‖_

pattern [∨]-introₗ l = Either.Left l
pattern [∨]-introᵣ r = Either.Right r

[∨]-elim : ∀{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} → (P → R) → (Q → R) → (P ∨ Q) → R
[∨]-elim = Either.map1

[∨]-elim2 = Either.map

------------------------------------------
-- Bottom (false, absurdity, empty, contradiction)

⊥ : Stmt{Lvl.𝟎}
⊥ = Empty

[⊥]-intro : ∀{P : Stmt{ℓ}} → P → (P → ⊥) → ⊥
[⊥]-intro = apply

[⊥]-elim : ∀{P : Stmt{ℓ}} → ⊥ → P
[⊥]-elim = empty

------------------------------------------
-- Top (true, truth, unit, validity)

⊤ : Stmt{Lvl.𝟎}
⊤ = Unit

pattern [⊤]-intro = <>

------------------------------------------
-- Negation

¬_ : Stmt{ℓ} → Stmt
¬_ = _→ᶠ ⊥

[¬]-intro : ∀{P : Stmt{ℓ}} → (P → ⊥) → (¬ P)
[¬]-intro = id

[¬]-elim : ∀{P : Stmt{ℓ}} → (¬ P) → (P → ⊥)
[¬]-elim = id

¬¬_ : Stmt{ℓ} → Stmt
¬¬_ = (_∘_) $₂ (¬_)

------------------------------------------
-- Exclusive disjunction (XOR)

data _⊕_ (P : Stmt{ℓ₁}) (Q : Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  [⊕]-introₗ : P → (¬ Q) → (P ⊕ Q)
  [⊕]-introᵣ : Q → (¬ P) → (P ⊕ Q)

------------------------------------------
-- Negative disjunction (NOR)

_⊽_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_⊽_ = (¬_) ∘₂ (_∨_)

------------------------------------------
-- Negative conjunction (NAND)

_⊼_ : Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_⊼_ = (¬_) ∘₂ (_∧_)
