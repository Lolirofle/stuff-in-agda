module Logic.Propositional.Theorems {ℓ} where

open import Data
open import Functional
open import Functional.Raise
open import Logic.Propositional{ℓ}
open import Type

[↔]-reflexivity : {X : Stmt} → (X ↔ X)
[↔]-reflexivity = [↔]-intro id id

[↔]-transitivity : ∀{X Y Z : Stmt} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
[↔]-transitivity {X}{Y}{Z} ([↔]-intro yx xy) ([↔]-intro zy yz) = [↔]-intro (yx ∘ zy) (yz ∘ xy)

[∧]-transitivity : ∀{X Y Z : Stmt} → (X ∧ Y) → (Y ∧ Z) → (X ∧ Z)
[∧]-transitivity ([∧]-intro x _) ([∧]-intro _ z) = [∧]-intro x z

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
[→]-syllogism = liftᵣ

------------------------------------------
-- Other

[→]-lift : {T X Y : Stmt} → (X → Y) → ((T → X) → (T → Y))
[→]-lift = liftₗ

material-impl₁ : {X Y : Stmt} → ((¬ X) ∨ Y) → (X → Y)
material-impl₁ = [∨]-elim ([→]-lift [⊥]-elim) ([→]-intro)
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
constructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

-- destructive-dilemma : {A B C D : Stmt} → (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
-- destructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

contrapositiveᵣ : {X Y : Stmt} → (X → Y) → ((¬ X) ← (¬ Y))
contrapositiveᵣ = [→]-syllogism
-- contrapositiveᵣ f ny = ny ∘ f

contrapositive₂ : {X Y : Stmt} → (X → (¬¬ Y)) ← ((¬ X) ← (¬ Y)) -- TODO: At least this works? Or am I missing something?
contrapositive₂ nf x = (swap nf) x
-- (¬ X) ← (¬ Y)
-- (¬ Y) → (¬ X)
-- (Y → ⊥) → (X → ⊥)
-- (Y → ⊥) → X → ⊥
-- X → (Y → ⊥) → ⊥
-- X → ((Y → ⊥) → ⊥)
-- X → (¬ (Y → ⊥))
-- X → (¬ (¬ Y))

contrapositive₃ : {X Y : Stmt} → (X → (¬ Y)) → ((¬ X) ← Y) -- TODO: Generalized variant of contrapositive₂
contrapositive₃ nf x = (swap nf) x

modus-tollens : {X Y : Stmt} → (X → Y) → (¬ Y) → (¬ X)
modus-tollens = contrapositiveᵣ

double-contrapositiveᵣ : {X Y : Stmt} → (X → Y) → ((¬¬ X) → (¬¬ Y))
double-contrapositiveᵣ = contrapositiveᵣ ∘ contrapositiveᵣ

[¬¬]-intro : {X : Stmt} → X → (¬¬ X)
[¬¬]-intro = apply
-- X → (X → ⊥) → ⊥

[¬¬¬]-elim : {X : Stmt} → (¬ (¬ (¬ X))) → (¬ X)
[¬¬¬]-elim = contrapositiveᵣ [¬¬]-intro
-- (((X → ⊥) → ⊥) → ⊥) → (X → ⊥)
-- (((X → ⊥) → ⊥) → ⊥) → X → ⊥
--   (A → B) → ((B → ⊥) → (A → ⊥)) //contrapositiveᵣ
--   (A → B) → (B → ⊥) → (A → ⊥)
--   (A → B) → (B → ⊥) → A → ⊥
--   (X → ((X → ⊥) → ⊥)) → (((X → ⊥) → ⊥) → ⊥) → X → ⊥ //A≔X , B≔((X → ⊥) → ⊥)

--   X → (¬ (¬ X)) //[¬¬]-intro
--   X → ((X → ⊥) → ⊥)

--   (((X → ⊥) → ⊥) → ⊥) → X → ⊥ //[→]-elim (Combining those two)
--   (((X → ⊥) → ⊥) → ⊥) → (X → ⊥)

[→]ₗ-[¬¬]-elim : {X Y : Stmt} → ((¬¬ X) → Y) → (X → Y)
[→]ₗ-[¬¬]-elim = liftᵣ([¬¬]-intro)

[→]ᵣ-[¬¬]-move-out  : ∀{X Y : Stmt} → (X → (¬¬ Y)) → ¬¬(X → Y)
[→]ᵣ-[¬¬]-move-out {X}{Y} (xnny) =
  (nxy ↦
    ([→]-elim
      ((x ↦
        (([⊥]-elim
          (([→]-elim
            ((y ↦
              (([→]-elim
                (([→]-intro y) :of: (X → Y))
                (nxy           :of: ¬(X → Y))
              ) :of: ⊥)
            ) :of: (¬ Y))
            (([→]-elim x xnny) :of: (¬¬ Y))
          ) :of: ⊥)
        ) :of: Y)
      ) :of: (X → Y))
      (nxy :of: ¬(X → Y))
    )
  )

[→][∧]ₗ : {X Y : Stmt} → (X → (¬¬ Y)) ← ¬(X ∧ (¬ Y))
[→][∧]ₗ = Tuple.curry
-- ¬(A ∧ ¬B) → (A → ¬¬B)
--   ¬(A ∧ (¬ B)) //assumption
--   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
--   (A → (B → ⊥) → ⊥) //Tuple.curry
--   (A → ¬(B → ⊥)) //Definition: (¬)
--   (A → ¬(¬ B)) //Definition: (¬)

[→][∧]ᵣ : {X Y : Stmt} → (X → Y) → ¬(X ∧ (¬ Y))
[→][∧]ᵣ f = Tuple.uncurry([¬¬]-intro ∘ f)

[↔]-of-[∧] : ∀{X Y Z} → ((X ∧ Z) ↔ (Y ∧ Z)) → (Z → (X ↔ Y))
[↔]-of-[∧] ([↔]-intro yzxz xzyz) z =
  ([↔]-intro
    (y ↦ [∧]-elimₗ(yzxz([∧]-intro y z)))
    (x ↦ [∧]-elimₗ(xzyz([∧]-intro x z)))
  )

[↔]-adding-[∧] : ∀{X Y Z} → (X ↔ Y) → ((X ∧ Z) ↔ (Y ∧ Z))
[↔]-adding-[∧] ([↔]-intro yx xy) =
  ([↔]-intro
    (yz ↦ [∧]-intro (yx([∧]-elimₗ yz)) ([∧]-elimᵣ yz))
    (xz ↦ [∧]-intro (xy([∧]-elimₗ xz)) ([∧]-elimᵣ xz))
  )

[↔]-elimₗ-[¬] : ∀{X Y} → (X ↔ Y) → (¬ X) → (¬ Y)
[↔]-elimₗ-[¬] xy nx y = nx([↔]-elimₗ(xy)(y))

[↔]-elimᵣ-[¬] : ∀{X Y} → (X ↔ Y) → (¬ Y) → (¬ X)
[↔]-elimᵣ-[¬] xy ny x = ny([↔]-elimᵣ(xy)(x))

[↔]-negative : ∀{X Y} → (X ↔ Y) → ((¬ X) ↔ (¬ Y))
[↔]-negative xy = [↔]-intro ([↔]-elimᵣ-[¬] (xy)) ([↔]-elimₗ-[¬] (xy))

[↔]-elim-[∨] : ∀{X Y} → (X ↔ Y) → (X ∨ Y) → (X ∧ Y)
[↔]-elim-[∨] (x↔y) ([∨]-introₗ x) = [∧]-intro x (([↔]-elimᵣ x↔y)(x))
[↔]-elim-[∨] (x↔y) ([∨]-introᵣ y) = [∧]-intro (([↔]-elimₗ x↔y)(y)) y

-- TODO: Is this possible to prove?
-- [↔]-elim-[¬∨¬] : ∀{X Y} → (X ↔ Y) → ((¬ X) ∨ (¬ Y)) → (X ∧ Y)

------------------------------------------
-- Almost-distributivity with duals (De-morgan's laws)

-- [¬][∧]ₗ : {X Y : Stmt} → ((¬ X) ∨ (¬ Y)) ← (¬ (X ∧ Y))
-- [¬][∧]ₗ n = -- TODO: Not possible in constructive logic? Seems to require ¬¬X=X?
-- ((X ∧ Y) → ⊥) → ((X → ⊥) ∨ (Y → ⊥))
-- ¬((X ∧ Y) → ⊥) ← ¬((X → ⊥) ∨ (Y → ⊥))

[¬][∧]ᵣ : {X Y : Stmt} → ((¬ X) ∨ (¬ Y)) → (¬ (X ∧ Y))
[¬][∧]ᵣ ([∨]-introₗ nx) = nx ∘ [∧]-elimₗ
[¬][∧]ᵣ ([∨]-introᵣ ny) = ny ∘ [∧]-elimᵣ
-- (X → ⊥) → (X ∧ Y) → ⊥
-- (Y → ⊥) → (X ∧ Y) → ⊥

[¬][∨] : {X Y : Stmt} → ((¬ X) ∧ (¬ Y)) ↔ (¬ (X ∨ Y))
[¬][∨] = [↔]-intro [¬][∨]₁ [¬][∨]₂
  where [¬][∨]₁ : {X Y : Stmt} → (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
        [¬][∨]₁ f = [∧]-intro (f ∘ [∨]-introₗ) (f ∘ [∨]-introᵣ)
        -- (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
        -- ((X ∨ Y) → ⊥) → ((X → ⊥) ∧ (Y → ⊥))

        [¬][∨]₂ : {X Y : Stmt} → ((¬ X)∧(¬ Y)) → ¬(X ∨ Y)
        [¬][∨]₂ ([∧]-intro nx ny) = [∨]-elim nx ny
        -- ((¬ X) ∧ (¬ Y)) → (¬ (X ∨ Y))
        -- ((X → ⊥) ∧ (Y → ⊥)) → ((X ∨ Y) → ⊥)
        -- ((X → ⊥) ∧ (Y → ⊥)) → (X ∨ Y) → ⊥
        -- (X → ⊥) → (Y → ⊥) → (X ∨ Y) → ⊥

------------------------------------------
-- Conjunction and implication (Tuples and functions)

[→][∧]-assumption : {X Y Z : Stmt} → ((X ∧ Y) → Z) ↔ (X → Y → Z)
[→][∧]-assumption = [↔]-intro Tuple.uncurry Tuple.curry

[→][∧]-distributivityₗ : {X Y Z : Stmt} → (X → (Y ∧ Z)) ↔ ((X → Y) ∧ (X → Z))
[→][∧]-distributivityₗ = [↔]-intro [→][∧]-distributivityₗ₁ [→][∧]-distributivityₗ₂
  where [→][∧]-distributivityₗ₁ : {X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) → (X → (Y ∧ Z))
        [→][∧]-distributivityₗ₁ ([∧]-intro xy xz) x = [∧]-intro (xy(x)) (xz(x))

        [→][∧]-distributivityₗ₂ : {X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) ← (X → (Y ∧ Z))
        [→][∧]-distributivityₗ₂ both = [∧]-intro ([∧]-elimₗ ∘ both) ([∧]-elimᵣ ∘ both)

-- (X ∧ Y) ∨ (X ∧ Z)
-- X → (Y ∨ Z)
-- X ∨ (Y ∧ Z)

non-contradiction : ∀{X : Stmt} → ¬(X ∧ (¬ X))
non-contradiction(x , nx) = nx x

------------------------------------------
-- Redundant formulas in operations

[→]-redundancy : ∀{A B : Stmt} → (A → A → B) → (A → B)
[→]-redundancy(f)(a) = f(a)(a)

[∧]-redundancy : ∀{A : Stmt} → (A ∧ A) ↔ A
[∧]-redundancy = [↔]-intro (x ↦ [∧]-intro(x)(x)) [∧]-elimₗ

[∨]-redundancy : ∀{A : Stmt} → (A ∨ A) ↔ A
[∨]-redundancy = [↔]-intro [∨]-introₗ (x ↦ [∨]-elim id id x)

------------------------------------------
-- Stuff related to classical logic

[¬¬]-excluded-middle : ∀{X} → ¬¬(X ∨ (¬ X))
[¬¬]-excluded-middle{X} =
  ([¬]-intro(naorna ↦
    ((non-contradiction([∧]-intro
      (([∨]-introᵣ
        (([¬]-intro(a ↦
          ((non-contradiction([∧]-intro
            (([∨]-introₗ a) :of:  (X ∨ (¬ X)))
            (naorna         :of: ¬(X ∨ (¬ X)))
          )) :of: ⊥)
        )) :of: (¬ X))
      ) :of: (X ∨ (¬ X)))
      (naorna :of: ¬(X ∨ (¬ X)))
    )) :of: ⊥)
  )) :of: ¬¬(X ∨ (¬ X))

[¬¬]-elim-from-excluded-middle : ∀{X} → (X ∨ (¬ X)) → ((¬¬ X) → X)
[¬¬]-elim-from-excluded-middle ([∨]-introₗ x)  (nnx) = x
[¬¬]-elim-from-excluded-middle ([∨]-introᵣ nx) (nnx) = [⊥]-elim(nnx(nx))

[[¬¬]-elim]-[excluded-middle]-eqₗ : (∀{X} → (¬¬ X) → X) ← (∀{X} → X ∨ (¬ X))
[[¬¬]-elim]-[excluded-middle]-eqₗ or {X} (nnx) with or
...                                           | ([∨]-introₗ x ) = x
...                                           | ([∨]-introᵣ nx) = [⊥]-elim(nnx(nx))

[[¬¬]-elim]-[excluded-middle]-eqᵣ : (∀{X} → (¬¬ X) → X) → (∀{X} → (X ∨ (¬ X)))
[[¬¬]-elim]-[excluded-middle]-eqᵣ (nnxx) = nnxx([¬¬]-excluded-middle)
