module LogicTheorems where

open import Data
open import Functional
open import Functional.Raise
open import Logic

------------------------------------------
-- Commutativity

[∧]-commutativity : {X Y : Stmt} → (X ∧ Y) → (Y ∧ X)
[∧]-commutativity ([∧]-intro x y) = [∧]-intro y x

[∨]-commutativity : {X Y : Stmt} → (X ∨ Y) → (Y ∨ X)
[∨]-commutativity ([∨]-introₗ x) = [∨]-introᵣ x
[∨]-commutativity ([∨]-introᵣ y) = [∨]-introₗ y

[↔]-commutativity : {X Y : Stmt} → (X ↔ Y) → (Y ↔ X)
[↔]-commutativity = [∧]-commutativity

------------------------------------------
-- Associativity

[∧]-associativity : {X Y Z : Stmt} → ((X ∧ Y) ∧ Z) → (X ∧ (Y ∧ Z))
[∧]-associativity ([∧]-intro ([∧]-intro x y) z) = [∧]-intro x ([∧]-intro y z)

[∨]-associativity : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) → (X ∨ (Y ∨ Z))
[∨]-associativity ([∨]-introₗ([∨]-introₗ x)) = [∨]-introₗ x
[∨]-associativity ([∨]-introₗ([∨]-introᵣ y)) = [∨]-introᵣ([∨]-introₗ y)
[∨]-associativity ([∨]-introᵣ z) = [∨]-introᵣ([∨]-introᵣ z)

------------------------------------------
-- Syllogism

[∨]-syllogism : {X Y : Stmt} → (X ∨ Y) → (¬ X) → Y
[∨]-syllogism ([∨]-introₗ x) nx = [⊥]-elim(nx x)
[∨]-syllogism ([∨]-introᵣ y) = [→]-intro y

[→]-syllogism : {X Y Z : Stmt} → (X → Y) → (Y → Z) → (X → Z)
[→]-syllogism = swap lift

------------------------------------------
-- Other

[→]-lift : {T X Y : Stmt} → (X → Y) → ((T → X) → (T → Y))
[→]-lift = lift

material-impl : ∀ {X Y : Stmt} → (¬ X) ∨ Y → (X → Y)
material-impl = ((Tuple.curry ∘ Tuple.curry) [∨]-elim) ([→]-lift [⊥]-elim) ([→]-intro)
-- material-impl ([∨]-introₗ nx) x = [⊥]-elim(nx x)
-- material-impl ([∨]-introₗ nx) = [⊥]-elim ∘ nx
-- material-impl ([∨]-introᵣ y) = [→]-intro y

-- material-impl2 : ∀ {X Y : Stmt} → (X → Y) → (¬ X) ∨ Y
-- material-impl2 f =

constructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
constructive-dilemma l r = ((Tuple.curry ∘ Tuple.curry) [∨]-elim) ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

-- destructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
-- destructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

contrapositive : {X Y : Stmt} → (X → Y) → ((¬ X) ← (¬ Y))
contrapositive f ny = [⊥]-elim ∘ ny ∘ f

-- contrapositive2 : {X Y : Stmt} → ((¬ X) ← (¬ Y)) → (X → Y)
-- contrapositive2 nf x = [⊥]-elim ∘ ((swap nf) x)
-- (¬ X) ← (¬ Y)
-- (¬ Y) → (¬ X)
-- (Y → ⊥) → X → ⊥
-- (Y → ⊥) → ⊥
-- (Y → Y) → X → ⊥
-- X → ⊥
-- X → Y

modus-tollens : {X Y : Stmt} → (X → Y) → (¬ Y) → (¬ X)
modus-tollens = contrapositive

------------------------------------------
-- Almost-distributivity with duals (De-morgan's laws)

-- [¬]-[∧]₁ : {X Y : Stmt} → (¬ (X ∧ Y)) → ((¬ X) ∨ (¬ Y))
-- [¬]-[∧]₁ n = -- TODO: Not possible in constructive logic? Seems to require ¬¬X=X?
-- ((X ∧ Y) → ⊥) → ((X → ⊥) ∨ (Y → ⊥))
-- ((X ∧ Y) → ⊥) → (X → ⊥)

[¬]-[∧]₂ : {X Y : Stmt} → ((¬ X) ∨ (¬ Y)) → (¬ (X ∧ Y))
[¬]-[∧]₂ ([∨]-introₗ nx) = nx ∘ [∧]-elimₗ
[¬]-[∧]₂ ([∨]-introᵣ ny) = ny ∘ [∧]-elimᵣ
-- (X → ⊥) → (X ∧ Y) → ⊥
-- (Y → ⊥) → (X ∧ Y) → ⊥

[¬]-[∨]₁ : {X Y : Stmt} → (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
[¬]-[∨]₁ f = [∧]-intro (f ∘ [∨]-introₗ) (f ∘ [∨]-introᵣ)
-- (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
-- ((X ∨ Y) → ⊥) → ((X → ⊥) ∧ (Y → ⊥))

[¬]-[∨]₂ : {X Y : Stmt} → ((¬ X) ∧ (¬ Y)) → (¬ (X ∨ Y))
[¬]-[∨]₂ ([∧]-intro nx ny) or = [∨]-elim(nx , ny , or)
-- ((¬ X) ∧ (¬ Y)) → (¬ (X ∨ Y))
-- ((X → ⊥) ∧ (Y → ⊥)) → ((X ∨ Y) → ⊥)
-- ((X → ⊥) ∧ (Y → ⊥)) → (X ∨ Y) → ⊥
-- (X → ⊥) → (Y → ⊥) → (X ∨ Y) → ⊥

------------------------------------------
-- Tuples and functions (Currying)

[∧]-[→] : {X Y Z : Stmt} → ((X ∧ Y) → Z) → (X → Y → Z)
[∧]-[→] and x y = and([∧]-intro x y)

[→]-[∧] : {X Y Z : Stmt} → (X → Y → Z) → ((X ∧ Y) → Z)
[→]-[∧] f ([∧]-intro x y) = f x y
