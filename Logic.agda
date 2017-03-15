module Logic level where

open import Data
open import Functional

infixl 10 _⇒_
infixl 1005 _∧_
infixl 1004 _∨_
infixl 1000 _←_ _↔_

------------------------------------------
-- Statement

Stmt = Set level

------------------------------------------
-- Conjunction (AND)

_∧_ : Stmt → Stmt → Stmt
_∧_ = _⨯_

pattern [∧]-intro x y = x , y

[∧]-elimₗ : {X Y : Stmt} → (X ∧ Y) → X
[∧]-elimₗ = Tuple.left

[∧]-elimᵣ : {X Y : Stmt} → (X ∧ Y) → Y
[∧]-elimᵣ = Tuple.right

------------------------------------------
-- Implication

[→]-elim : {X Y : Stmt} → (X ⨯ (X → Y)) → Y
[→]-elim = Tuple.uncurry apply

[→]-intro : {X Y : Stmt} → Y → (X → Y)
[→]-intro = const

------------------------------------------
-- Reverse implication

_←_ : Stmt → Stmt → Stmt
y ← x = x → y

[←]-intro : {X Y : Stmt} → Y → (Y ← X)
[←]-intro = [→]-intro

[←]-elim : {X Y : Stmt} → (X ⨯ (Y ← X)) → Y
[←]-elim = [→]-elim

------------------------------------------
-- Equivalence

_↔_ : Stmt → Stmt → Stmt
x ↔ y = ((x ← y) ⨯ (x → y))

pattern [↔]-intro l r = l , r

[↔]-elimₗ : {X Y : Stmt} → (X ↔ Y) → (X ← Y)
[↔]-elimₗ = Tuple.left

[↔]-elimᵣ : {X Y : Stmt} → (X ↔ Y) → (X → Y)
[↔]-elimᵣ = Tuple.right

------------------------------------------
-- Disjunction (OR)

_∨_ : Stmt → Stmt → Stmt
_∨_ = _‖_

pattern [∨]-introₗ l = Either.Left l
pattern [∨]-introᵣ r = Either.Right r

[∨]-elim : {X Y Z : Stmt} → ((X → Z) ⨯ (Y → Z) ⨯ (X ∨ Y)) → Z
[∨]-elim(f₁ , _ , (Either.Left x)) = f₁ x
[∨]-elim(_ , f₂ , (Either.Right y)) = f₂ y

------------------------------------------
-- Bottom (false, absurdity, empty)

data ⊥ : Stmt where

[⊥]-elim : {X : Stmt} → ⊥ → X
[⊥]-elim ()

------------------------------------------
-- Top (true, truth, unit)

data ⊤ : Stmt where
  [⊤]-intro : ⊤

------------------------------------------
-- Negation

¬_ : Stmt → Stmt
¬ x = x → ⊥

[¬]-intro : {X : Stmt} → (X → ⊥) → ¬ X
[¬]-intro = id

[¬]-elim : {X : Stmt} → ¬ X → (X → ⊥) -- written like (X → (¬ X) → ⊥) looks like a [⊥]-intro
[¬]-elim = id

[¬¬]-intro : {X : Stmt} → X → (¬ (¬ X))
[¬¬]-intro = apply
-- X → (X → ⊥) → ⊥

------------------------------------------
-- Exclusive disjunction (XOR)

-- data _⊕_ {X : Stmt} {Y : Stmt} : Stmt where
--   [⊕]-introₗ X → ¬(X ∧ Y) → (X ⊕ Y)
--   [⊕]-introᵣ Y → ¬(X ∧ Y) → (X ⊕ Y)
-- 
-- [⊕]-elim : {X Y : Stmt} → (X ⊕ Y) → (X ↔ Y) → ⊥
-- [⊕]-elim ([⊕]-introₗ x nxy)

------------------------------------------
-- Negative disjunction (NOR)

_⊽_ : Stmt → Stmt → Stmt
x ⊽ y = (¬ x) ∧ (¬ y)

pattern [⊽]-intro x y = [∧]-intro x y

[⊽]-elimₗ : {X Y : Stmt} → (X ⊽ Y) → ¬ X
[⊽]-elimₗ = [∧]-elimₗ

[⊽]-elimᵣ : {X Y : Stmt} → (X ⊽ Y) → ¬ Y
[⊽]-elimᵣ = [∧]-elimᵣ

------------------------------------------
-- Negative conjunction (NAND)

-- data _⊼_ {X : Stmt} {Y : Stmt} : Stmt where
--   [⊼]-intro ¬(X ∧ Y) → (X ⊼ Y)
-- 
-- [⊼]-elim : {X Y : Stmt} → (X ⨯ Y ⨯ (X ⊼ Y)) → ⊥
-- [⊼]-elim(x , y , nand)

------------------------------------------
-- Convenient definitions with different semantics

_⇒_ : {X Y : Stmt} → X → (X → Y) → Y
_⇒_ = apply
