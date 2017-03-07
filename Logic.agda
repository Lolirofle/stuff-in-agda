module Logic where

open import Functional

------------------------------------------
-- Statement
Stmt = Set

------------------------------------------
-- Conjunction
data _∧_ (X : Stmt) (Y : Stmt) : Stmt where
  [∧]-intro : X → Y → (X ∧ Y)

[∧]-elimₗ : {X Y : Stmt} → (X ∧ Y) → X
[∧]-elimₗ ([∧]-intro x _) = x

[∧]-elimᵣ : {X Y : Stmt} → (X ∧ Y) → Y
[∧]-elimᵣ ([∧]-intro _ y) = y

------------------------------------------
-- Implication
[→]-elim : {X Y : Stmt} → X → (X → Y) → Y
[→]-elim = apply

[→]-intro : {X Y : Stmt} → Y → (X → Y)
[→]-intro = const

------------------------------------------
-- Reverse implication
_←_ : Stmt → Stmt → Stmt
y ← x = x → y

[←]-elim : {X Y : Stmt} → X → (Y ← X) → Y
[←]-elim = apply

[←]-intro : {X Y : Stmt} → Y → (Y ← X)
[←]-intro = const

------------------------------------------
-- Equivalence
_↔_ : Stmt → Stmt → Stmt
x ↔ y = (y → x) ∧ (x → y)

[↔]-elimₗ : {X Y : Stmt} → (X ↔ Y) → Y → X
[↔]-elimₗ = [∧]-elimₗ

[↔]-elimᵣ : {X Y : Stmt} → (X ↔ Y) → X → Y
[↔]-elimᵣ = [∧]-elimᵣ

------------------------------------------
-- Disjunction
data _∨_ (X : Stmt) (Y : Stmt) : Stmt where
  [∨]-introₗ : X → (X ∨ Y)
  [∨]-introᵣ : Y → (X ∨ Y)

[∨]-elim : {X Y Z : Stmt} → (X → Z) → (Y → Z) → (X ∨ Y) → Z
[∨]-elim f₁ _ ([∨]-introₗ x) = f₁ x
[∨]-elim _ f₂ ([∨]-introᵣ y) = f₂ y

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
[¬]-intro x = x

[¬]-elim : {X : Stmt} → ¬ X → (X → ⊥) -- written like (X → (¬ X) → ⊥) looks like a [⊥]-intro
[¬]-elim x = x

[¬¬]-intro : {X : Stmt} → X → (¬ (¬ X))
[¬¬]-intro x f = f x
-- X → (X → ⊥) → ⊥

------------------------------------------
-- Convenient definitions with different semantics



infixl 0 _⇒_
_⇒_ : {X Y : Stmt} → X → (X → Y) → Y
_⇒_ = [→]-elim

------------------------------------------
-- Theorems
[∧]-commutativity : {X Y : Stmt} → (X ∧ Y) → (Y ∧ X)
[∧]-commutativity ([∧]-intro x y) = [∧]-intro y x

[∨]-commutativity : {X Y : Stmt} → (X ∨ Y) → (Y ∨ X)
[∨]-commutativity ([∨]-introₗ x) = [∨]-introᵣ x
[∨]-commutativity ([∨]-introᵣ y) = [∨]-introₗ y

[∧]-associativity : {X Y Z : Stmt} → ((X ∧ Y) ∧ Z) → (X ∧ (Y ∧ Z))
[∧]-associativity ([∧]-intro ([∧]-intro x y) z) = [∧]-intro x ([∧]-intro y z)

[∨]-associativity : {X Y Z : Stmt} → ((X ∨ Y) ∨ Z) → (X ∨ (Y ∨ Z))
[∨]-associativity ([∨]-introₗ([∨]-introₗ x)) = [∨]-introₗ x
[∨]-associativity ([∨]-introₗ([∨]-introᵣ y)) = [∨]-introᵣ([∨]-introₗ y)
[∨]-associativity ([∨]-introᵣ z) = [∨]-introᵣ([∨]-introᵣ z)

[↔]-commutativity : {X Y : Stmt} → (X ↔ Y) → (Y ↔ X)
[↔]-commutativity = [∧]-commutativity

[→]-lift : {T X Y : Stmt} → (X → Y) → ((T → X) → (T → Y))
[→]-lift = lift

material-impl : ∀ {X Y : Stmt} → (¬ X) ∨ Y → (X → Y)
material-impl = [∨]-elim ([→]-lift [⊥]-elim) ([→]-intro)
-- material-impl ([∨]-introₗ nx) x = [⊥]-elim(nx x)
-- material-impl ([∨]-introₗ nx) = [⊥]-elim ∘ nx
-- material-impl ([∨]-introᵣ y) = [→]-intro y

-- material-impl2 : ∀ {X Y : Stmt} → (X → Y) → (¬ X) ∨ Y
-- material-impl2 f =

[∨]-syllogism : {X Y : Stmt} → (X ∨ Y) → (¬ X) → Y
[∨]-syllogism ([∨]-introₗ x) nx = [⊥]-elim(nx x)
[∨]-syllogism ([∨]-introᵣ y) = [→]-intro y

[→]-syllogism : {X Y Z : Stmt} → (X → Y) → (Y → Z) → (X → Z)
[→]-syllogism = swap lift

constructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
constructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

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
[¬]-[∨]₂ ([∧]-intro nx ny) or = [∨]-elim nx ny or
-- ((¬ X) ∧ (¬ Y)) → (¬ (X ∨ Y))
-- ((X → ⊥) ∧ (Y → ⊥)) → ((X ∨ Y) → ⊥)
-- ((X → ⊥) ∧ (Y → ⊥)) → (X ∨ Y) → ⊥
-- (X → ⊥) → (Y → ⊥) → (X ∨ Y) → ⊥

[∧]-[→] : {X Y Z : Stmt} → ((X ∧ Y) → Z) → (X → Y → Z)
[∧]-[→] and x y = and([∧]-intro x y)

[→]-[∧] : {X Y Z : Stmt} → (X → Y → Z) → ((X ∧ Y) → Z)
[→]-[∧] f ([∧]-intro x y) = f x y
