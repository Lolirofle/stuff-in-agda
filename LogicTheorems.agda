module LogicTheorems level where

open import Data
open import Functional
open import Functional.Raise
open import Logic(level)

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

[∧]-associativity : {X Y Z : Stmt} → ((X ∧ Y) ∧ Z) ↔ (X ∧ (Y ∧ Z))
[∧]-associativity = [↔]-intro [∧]-associativity₁ [∧]-associativity₂
  where [∧]-associativity₁ : {X Y Z : Stmt} → ((X ∧ Y) ∧ Z) ← (X ∧ (Y ∧ Z))
        [∧]-associativity₁ ([∧]-intro x ([∧]-intro y z)) = [∧]-intro ([∧]-intro x y) z

        [∧]-associativity₂ : {X Y Z : Stmt} → ((X ∧ Y) ∧ Z) → (X ∧ (Y ∧ Z))
        [∧]-associativity₂ ([∧]-intro ([∧]-intro x y) z) = [∧]-intro x ([∧]-intro y z)

[∨]-associativity : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ↔ (X ∨ (Y ∨ Z))
[∨]-associativity = [↔]-intro [∨]-associativity₁ [∨]-associativity₂
  where [∨]-associativity₁ : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ← (X ∨ (Y ∨ Z))
        [∨]-associativity₁ ([∨]-introₗ x) = [∨]-introₗ([∨]-introₗ x)
        [∨]-associativity₁ ([∨]-introᵣ([∨]-introₗ y)) = [∨]-introₗ([∨]-introᵣ y)
        [∨]-associativity₁ ([∨]-introᵣ([∨]-introᵣ z)) = [∨]-introᵣ z

        [∨]-associativity₂ : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) → (X ∨ (Y ∨ Z))
        [∨]-associativity₂ ([∨]-introₗ([∨]-introₗ x)) = [∨]-introₗ x
        [∨]-associativity₂ ([∨]-introₗ([∨]-introᵣ y)) = [∨]-introᵣ([∨]-introₗ y)
        [∨]-associativity₂ ([∨]-introᵣ z) = [∨]-introᵣ([∨]-introᵣ z)

        -- [∨]-associativity₂ : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ← (X ∨ (Y ∨ Z))
        -- [∨]-associativity₂ {X} {Y} {Z} stmt = [∨]-associativity₁ {Y} {Z} {X} ([∨]-commutativity {X} {Y ∨ Z} stmt)

-- [↔]-associativity : {X Y Z : Stmt} → ((X ↔ Y) ↔ Z) → (X ↔ (Y ↔ Z))
-- [↔]-associativity = 
-- (Z → (X ↔ Y) , (X ↔ Y) → Z) → (X ↔ (Y ↔ Z))
-- (Z → (X ↔ Y) , (X ↔ Y) → Z) → (X → (Y ↔ Z) , (Y ↔ Z) → X)
-- (Z → (X → Y , Y → X) , (X → Y , Y → X) → Z) → (X → (Y → Z , Z → Y) , (Y → Z , Z → Y) → X)
-- ((Z → (X → Y) , Z → (Y → X)) , (X → Y , Y → X) → Z) → ((X → (Y → Z) , X → (Z → Y)) , (Y → Z , Z → Y) → X)
-- ((Z → X → Y , Z → Y → X) , (X → Y , Y → X) → Z) → ((X → Y → Z , X → Z → Y) , (Y → Z , Z → Y) → X)
-- ((X → Z → Y , Y → Z → X) , (X → Y , Y → X) → Z) → ((X → Y → Z , X → Z → Y) , (Y → Z , Z → Y) → X)
-- ((Y → Z → X , X → Z → Y) , (X → Y , Y → X) → Z) → ((X → Y → Z , X → Z → Y) , (Y → Z , Z → Y) → X)

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

material-impl₁ : {X Y : Stmt} → ((¬ X) ∨ Y) → (X → Y)
material-impl₁ = ((Tuple.curry ∘ Tuple.curry) [∨]-elim) ([→]-lift [⊥]-elim) ([→]-intro)
-- ((¬ X) ∨ Y)
-- ((X → ⊥) ∨ Y)
-- ((X → ⊥) ∨ (X → Y))
-- ((X → Y) ∨ (X → Y))
-- (X → Y)

-- material-impl₂ : {X Y : Stmt} → (X → Y) → ((¬ X) ∨ Y) -- TODO: This does not work either?
-- material-impl₂ xy = 
-- (X → Y)
-- ?

-- ??? : {X Y : Stmt} → (X → Y) → (¬ (X ∧ (¬ Y))) -- TODO: This does not work either?
-- (¬ (X ∧ (¬ Y)))
-- ((X ∧ (Y → ⊥)) → ⊥)
-- ?

constructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
constructive-dilemma l r = ((Tuple.curry ∘ Tuple.curry) [∨]-elim) ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

-- destructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
-- destructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

contrapositive₁ : {X Y : Stmt} → (X → Y) → ((¬ X) ← (¬ Y))
contrapositive₁ = [→]-syllogism
-- contrapositive₁ f ny = ny ∘ f

contrapositive₂ : {X Y : Stmt} → (X → (¬ (¬ Y))) ← ((¬ X) ← (¬ Y)) -- TODO: At least this works? Or am I missing something?
contrapositive₂ nf x = (swap nf) x
-- (¬ X) ← (¬ Y)
-- (¬ Y) → (¬ X)
-- (Y → ⊥) → (X → ⊥)
-- (Y → ⊥) → X → ⊥
-- X → (Y → ⊥) → ⊥
-- X → ((Y → ⊥) → ⊥)
-- X → (¬ (Y → ⊥))
-- X → (¬ (¬ Y))

modus-tollens : {X Y : Stmt} → (X → Y) → (¬ Y) → (¬ X)
modus-tollens = contrapositive₁

[¬¬]-intro : {X : Stmt} → X → (¬ (¬ X))
[¬¬]-intro = apply
-- X → (X → ⊥) → ⊥

[¬¬¬]-elim : {X : Stmt} → (¬ (¬ (¬ X))) → (¬ X)
[¬¬¬]-elim = contrapositive₁ [¬¬]-intro
-- (((X → ⊥) → ⊥) → ⊥) → (X → ⊥)
-- (((X → ⊥) → ⊥) → ⊥) → X → ⊥
--   (A → B) → ((B → ⊥) → (A → ⊥)) //contrapositive₁
--   (A → B) → (B → ⊥) → (A → ⊥)
--   (A → B) → (B → ⊥) → A → ⊥

--   X → (¬ (¬ X)) //[¬¬]-intro
--   X → ((X → ⊥) → ⊥)

--   (X → ((X → ⊥) → ⊥)) → (((X → ⊥) → ⊥) → ⊥) → X → ⊥ //Combining those two (A=X , B=((X → ⊥) → ⊥))

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

[¬]-[∨] : {X Y : Stmt} → ((¬ X) ∧ (¬ Y)) ↔ (¬ (X ∨ Y))
[¬]-[∨] = [↔]-intro [¬]-[∨]₁ [¬]-[∨]₂
  where [¬]-[∨]₁ : {X Y : Stmt} → (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
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
-- Conjunction and implication (Tuples and functions)

[∧]↔[→]-in-assumption : {X Y Z : Stmt} → ((X ∧ Y) → Z) ↔ (X → Y → Z)
[∧]↔[→]-in-assumption = [↔]-intro Tuple.uncurry Tuple.curry

[→]-left-distributivity-over-[∧] : {X Y Z : Stmt} → (X → (Y ∧ Z)) ↔ ((X → Y) ∧ (X → Z))
[→]-left-distributivity-over-[∧] = [↔]-intro [→]-left-distributivity-over-[∧]₁ [→]-left-distributivity-over-[∧]₂
  where [→]-left-distributivity-over-[∧]₁ : {X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) → (X → (Y ∧ Z))
        [→]-left-distributivity-over-[∧]₁ ([∧]-intro xy xz) x = [∧]-intro (xy(x)) (xz(x))

        [→]-left-distributivity-over-[∧]₂ : {X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) ← (X → (Y ∧ Z))
        [→]-left-distributivity-over-[∧]₂ both = [∧]-intro ([∧]-elimₗ ∘ both) ([∧]-elimᵣ ∘ both)

-- (X ∧ Y) ∨ (X ∧ Z)
-- X → (Y ∨ Z)
-- X ∨ (Y ∧ Z)

non-contradiction : {X : Stmt} → ¬ (X ∧ (¬ X))
non-contradiction(x , nx) = nx x
