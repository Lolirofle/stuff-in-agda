module Logic where

open import Data
open import Functional

------------------------------------------
-- Statement

Stmt = Set

------------------------------------------
-- Conjunction

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
[→]-elim(x , f) = f(x)

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
-- Disjunction

_∨_ : Stmt →  Stmt → Stmt
_∨_ = _‖_

pattern [∨]-introₗ l = Left l
pattern [∨]-introᵣ r = Right r

[∨]-elim : {X Y Z : Stmt} → ((X → Z) ⨯ (Y → Z) ⨯ (X ∨ Y)) → Z
[∨]-elim(f₁ , _ , (Left x)) = f₁ x
[∨]-elim(_ , f₂ , (Right y)) = f₂ y

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
-- Convenient definitions with different semantics

infixl 0 _⇒_
_⇒_ : {X Y : Stmt} → X → (X → Y) → Y
_⇒_ = apply
