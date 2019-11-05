module Logic.Propositional where

open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
import      Lvl
open import Type

infixl 1010 ¬_ ¬¬_
infixl 1005 _∧_
infixl 1004 _∨_
infixl 1000 _↔_

------------------------------------------
-- Conjunction (AND)

_∧_ : ∀{ℓ₁ ℓ₂} → Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_∧_ = _⨯_

pattern [∧]-intro p q = p , q

[∧]-elimₗ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ∧ Q) → P
[∧]-elimₗ = Tuple.left

[∧]-elimᵣ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ∧ Q) → Q
[∧]-elimᵣ = Tuple.right

[∧]-map = Tuple.map

------------------------------------------
-- Implication

[→]-elim : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (P → Q) → Q
[→]-elim p f = f(p)

[→]-intro : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P → Q) → (P → Q)
[→]-intro f(p) = f(p)

------------------------------------------
-- Reverse implication

open Functional using (_←_) public

[←]-intro : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P → Q) → (Q ← P)
[←]-intro = [→]-intro

[←]-elim : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (Q ← P) → Q
[←]-elim = [→]-elim

------------------------------------------
-- Equivalence

_↔_ : ∀{ℓ₁ ℓ₂} → Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
P ↔ Q = ((P ← Q) ⨯ (P → Q))

pattern [↔]-intro l r = l , r

[↔]-elimₗ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → Q → (P ↔ Q) → P
[↔]-elimₗ = swap Tuple.left

[↔]-elimᵣ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → P → (P ↔ Q) → Q
[↔]-elimᵣ = swap Tuple.right

[↔]-to-[←] : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ↔ Q) → (Q → P)
[↔]-to-[←] = Tuple.left

[↔]-to-[→] : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ↔ Q) → (P → Q)
[↔]-to-[→] = Tuple.right

------------------------------------------
-- Disjunction (OR)

_∨_ : ∀{ℓ₁ ℓ₂} → Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
_∨_ = _‖_

pattern [∨]-introₗ l = Either.Left l
pattern [∨]-introᵣ r = Either.Right r

[∨]-elim : ∀{ℓ₁ ℓ₂ ℓ₃}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} → (P → R) → (Q → R) → (P ∨ Q) → R
[∨]-elim(f₁) (_) (Either.Left p) = f₁ p
[∨]-elim(_) (f₂) (Either.Right q) = f₂ q

[∨]-map = Either.map2

------------------------------------------
-- Bottom (false, absurdity, empty, contradiction)

⊥ : Stmt{Lvl.𝟎}
⊥ = Empty

[⊥]-intro : ∀{ℓ}{P : Stmt{ℓ}} → P → (P → ⊥) → ⊥
[⊥]-intro = apply

[⊥]-elim : ∀{ℓ}{P : Stmt{ℓ}} → ⊥ → P
[⊥]-elim = empty

------------------------------------------
-- Top (true, truth, unit, validity)

⊤ : Stmt{Lvl.𝟎}
⊤ = Unit

pattern [⊤]-intro = <>

------------------------------------------
-- Negation

¬_ : ∀{ℓ} → Stmt{ℓ} → Stmt
¬_ {ℓ} T = (T → ⊥)

[¬]-intro : ∀{ℓ}{P : Stmt{ℓ}} → (P → ⊥) → (¬ P)
[¬]-intro = id

[¬]-elim : ∀{ℓ}{P : Stmt{ℓ}} → (¬ P) → (P → ⊥) -- written like (P → (¬ P) → ⊥) looks like a [⊥]-intro
[¬]-elim = id

¬¬_ : ∀{ℓ} → Stmt{ℓ} → Stmt
¬¬ p = ¬(¬ p)

------------------------------------------
-- Exclusive disjunction (XOR)

data _⊕_ {ℓ₁ ℓ₂} (P : Stmt{ℓ₁}) (Q : Stmt{ℓ₂}) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
  [⊕]-introₗ : P → (¬ Q) → (P ⊕ Q)
  [⊕]-introᵣ : Q → (¬ P) → (P ⊕ Q)

------------------------------------------
-- Negative disjunction (NOR)

_⊽_ : ∀{ℓ₁ ℓ₂} → Stmt{ℓ₁} → Stmt{ℓ₂} → Stmt
p ⊽ q = (¬ p) ∧ (¬ q)

pattern [⊽]-intro p q = [∧]-intro p q

[⊽]-elimₗ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ⊽ Q) → ¬ P
[⊽]-elimₗ = [∧]-elimₗ

[⊽]-elimᵣ : ∀{ℓ₁ ℓ₂}{P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} → (P ⊽ Q) → ¬ Q
[⊽]-elimᵣ = [∧]-elimᵣ

------------------------------------------
-- Negative conjunction (NAND)

-- data _⊼_ {P : Stmt} {Q : Stmt} : Stmt where
--   [⊼]-intro ¬(P ∧ Q) → (P ⊼ Q)
-- 
-- [⊼]-elim : {P Q : Stmt} → (P ⨯ Q ⨯ (P ⊼ Q)) → ⊥
-- [⊼]-elim(p , q , nand)
