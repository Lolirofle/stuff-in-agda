module Logic where

------------------------------------------
-- Conjunction
data _∧_ (X : Set) (Y : Set) : Set where
  [∧]-intro : X → Y → (X ∧ Y)

[∧]-elimₗ : {X : Set} → {Y : Set} → (X ∧ Y) → X
[∧]-elimₗ ([∧]-intro x _) = x

[∧]-elimᵣ : {X : Set} → {Y : Set} → (X ∧ Y) → Y
[∧]-elimᵣ ([∧]-intro _ y) = y

infixl 2 _,_
_,_ : {X : Set} → {Y : Set} → X → Y → X ∧ Y
x , y = [∧]-intro x y

------------------------------------------
-- Implication
[→]-elim : {X : Set} → {Y : Set} → X → (X → Y) → Y
[→]-elim x f = f x

infixl 0 _⇒_
_⇒_ : {X : Set} → {Y : Set} → X → (X → Y) → Y
x ⇒ f = [→]-elim x f

------------------------------------------
-- Equivalence
_↔_ : (X : Set) → (Y : Set) → Set
x ↔ y = (x → y) ∧ (y → x)

------------------------------------------
-- Disjunction
-- _∨_ : (X : Set) → (Y : Set) → Set
