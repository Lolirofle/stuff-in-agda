module Logic.Propositional.Theorems {ℓ} where

open import Data
open import Functional
open import Functional.Raise
open import Logic.Propositional{ℓ}
open import Type

------------------------------------------
-- Reflexivity

[↔]-reflexivity : ∀{X : Stmt} → (X ↔ X)
[↔]-reflexivity = [↔]-intro id id

[→]-reflexivity : ∀{X : Stmt} → (X → X)
[→]-reflexivity = id

------------------------------------------
-- Transitivity

[→]-transitivity : ∀{X Y Z : Stmt} → (X → Y) → (Y → Z) → (X → Z)
[→]-transitivity = swap _∘_

[↔]-transitivity : ∀{X Y Z : Stmt} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
[↔]-transitivity {X}{Y}{Z} ([↔]-intro yx xy) ([↔]-intro zy yz) = [↔]-intro (yx ∘ zy) (yz ∘ xy)

[∧]-transitivity : ∀{X Y Z : Stmt} → (X ∧ Y) → (Y ∧ Z) → (X ∧ Z)
[∧]-transitivity ([∧]-intro x _) ([∧]-intro _ z) = [∧]-intro x z

------------------------------------------
-- Symmetry

[∧]-symmetry : ∀{X Y : Stmt} → (X ∧ Y) → (Y ∧ X)
[∧]-symmetry ([∧]-intro x y) = [∧]-intro y x

[∨]-symmetry : ∀{X Y : Stmt} → (X ∨ Y) → (Y ∨ X)
[∨]-symmetry ([∨]-introₗ x) = [∨]-introᵣ x
[∨]-symmetry ([∨]-introᵣ y) = [∨]-introₗ y

[↔]-symmetry : ∀{X Y : Stmt} → (X ↔ Y) → (Y ↔ X)
[↔]-symmetry = [∧]-symmetry

------------------------------------------
-- Operators that implies other ones

[∧]-implies-[↔] : ∀{X Y : Stmt} → (X ∧ Y) → (X ↔ Y)
[∧]-implies-[↔] ([∧]-intro x y) = [↔]-intro (const x) (const y)

[∧]-implies-[→] : ∀{X Y : Stmt} → (X ∧ Y) → (X → Y)
[∧]-implies-[→] ([∧]-intro x y) = const y

[∧]-implies-[←] : ∀{X Y : Stmt} → (X ∧ Y) → (X ← Y)
[∧]-implies-[←] ([∧]-intro x y) = const x

------------------------------------------
-- Associativity (with respect to ↔)

[∧]-associativity : ∀{X Y Z : Stmt} → ((X ∧ Y) ∧ Z) ↔ (X ∧ (Y ∧ Z))
[∧]-associativity = [↔]-intro [∧]-associativity₁ [∧]-associativity₂
  where [∧]-associativity₁ : ∀{X Y Z : Stmt} → ((X ∧ Y) ∧ Z) ← (X ∧ (Y ∧ Z))
        [∧]-associativity₁ ([∧]-intro x ([∧]-intro y z)) = [∧]-intro ([∧]-intro x y) z

        [∧]-associativity₂ : ∀{X Y Z : Stmt} → ((X ∧ Y) ∧ Z) → (X ∧ (Y ∧ Z))
        [∧]-associativity₂ ([∧]-intro ([∧]-intro x y) z) = [∧]-intro x ([∧]-intro y z)

[∨]-associativity : ∀{X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ↔ (X ∨ (Y ∨ Z))
[∨]-associativity = [↔]-intro [∨]-associativity₁ [∨]-associativity₂
  where [∨]-associativity₁ : ∀{X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ← (X ∨ (Y ∨ Z))
        [∨]-associativity₁ ([∨]-introₗ x) = [∨]-introₗ([∨]-introₗ x)
        [∨]-associativity₁ ([∨]-introᵣ([∨]-introₗ y)) = [∨]-introₗ([∨]-introᵣ y)
        [∨]-associativity₁ ([∨]-introᵣ([∨]-introᵣ z)) = [∨]-introᵣ z

        [∨]-associativity₂ : ∀{X Y Z : Stmt} → ((X ∨ Y) ∨ Z) → (X ∨ (Y ∨ Z))
        [∨]-associativity₂ ([∨]-introₗ([∨]-introₗ x)) = [∨]-introₗ x
        [∨]-associativity₂ ([∨]-introₗ([∨]-introᵣ y)) = [∨]-introᵣ([∨]-introₗ y)
        [∨]-associativity₂ ([∨]-introᵣ z) = [∨]-introᵣ([∨]-introᵣ z)

        -- [∨]-associativity₂ : ∀{X Y Z : Stmt} → ((X ∨ Y) ∨ Z) ← (X ∨ (Y ∨ Z))
        -- [∨]-associativity₂ {X} {Y} {Z} stmt = [∨]-associativity₁ {Y} {Z} {X} ([∨]-symmetry {X} {Y ∨ Z} stmt)

[↔]-associativity : ∀{X Y Z : Stmt} → ((X ↔ Y) ↔ Z) ↔ (X ↔ (Y ↔ Z))
[↔]-associativity {X}{Y}{Z} = [↔]-intro [↔]-associativityₗ [↔]-associativityᵣ where
  [↔]-associativityₗ : ((X ↔ Y) ↔ Z) ← (X ↔ (Y ↔ Z))
  [↔]-associativityₗ ([↔]-intro yz2x x2yz) = [↔]-intro z2xy xy2z where
    z2xy : (X ↔ Y) ← Z
    z2xy z = [↔]-intro y2x x2y where
      y2x : Y → X
      y2x y = yz2x([∧]-implies-[↔]([∧]-intro y z))

      x2y : X → Y
      x2y x = [↔]-elimₗ (x2yz(x)) (z)

    postulate xy2z : (X ↔ Y) → Z -- TODO: How?
    -- xy2z ([↔]-intro y2x x2y) = ([↔]-elimᵣ (x2yz(x))) (y)

  [↔]-associativityᵣ : ((X ↔ Y) ↔ Z) → (X ↔ (Y ↔ Z))
  [↔]-associativityᵣ ([↔]-intro z2xy xy2z) = [↔]-intro yz2x x2yz where
    postulate yz2x : X ← (Y ↔ Z)
    -- yz2x ([↔]-intro z2y y2z) = 

    x2yz : X → (Y ↔ Z)
    x2yz x = [↔]-intro z2y y2z where
      z2y : Z → Y
      z2y z = [↔]-elimᵣ (z2xy(z)) (x)

      y2z : Y → Z
      y2z y = xy2z([∧]-implies-[↔]([∧]-intro x y))

------------------------------------------
-- Identity (with respect to ↔)

[∧]-identityₗ : ∀{X : Stmt} → (⊤ ∧ X) → X
[∧]-identityₗ ([∧]-intro _ x) = x

[∧]-identityᵣ : ∀{X : Stmt} → (X ∧ ⊤) → X
[∧]-identityᵣ ([∧]-intro x _) = x

[∨]-identityₗ : ∀{X : Stmt} → (⊥ ∨ X) → X
[∨]-identityₗ ([∨]-introₗ ())
[∨]-identityₗ ([∨]-introᵣ x) = x

[∨]-identityᵣ : ∀{X : Stmt} → (X ∨ ⊥) → X
[∨]-identityᵣ ([∨]-introₗ x) = x
[∨]-identityᵣ ([∨]-introᵣ ())

[→]-identityₗ : ∀{X : Stmt} → (⊤ → X) → X
[→]-identityₗ f = f([⊤]-intro)

[∧]-nullifierₗ : ∀{X : Stmt} → (⊥ ∧ X) → ⊥
[∧]-nullifierₗ ([∧]-intro () _)

[∧]-nullifierᵣ : ∀{X : Stmt} → (X ∧ ⊥) → ⊥
[∧]-nullifierᵣ ([∧]-intro _ ())

[⊤]-as-nullifierₗ : ∀{_▫_ : Stmt → Stmt → Stmt}{X : Stmt} → (⊤ ▫ X) → ⊤
[⊤]-as-nullifierₗ _ = [⊤]-intro

[⊤]-as-nullifierᵣ : ∀{_▫_ : Stmt → Stmt → Stmt}{X : Stmt} → (X ▫ ⊤) → ⊤
[⊤]-as-nullifierᵣ _ = [⊤]-intro

------------------------------------------
-- Syllogism

[∨]-syllogism : ∀{X Y : Stmt} → (X ∨ Y) → (¬ X) → Y
[∨]-syllogism ([∨]-introₗ x) nx = [⊥]-elim(nx x)
[∨]-syllogism ([∨]-introᵣ y) = [→]-intro y

[→]-syllogism : ∀{X Y Z : Stmt} → (X → Y) → (Y → Z) → (X → Z)
[→]-syllogism = liftᵣ

------------------------------------------
-- Other

[→]-lift : ∀{T X Y : Stmt} → (X → Y) → ((T → X) → (T → Y))
[→]-lift = liftₗ

material-implₗ : ∀{X Y : Stmt} → (X → Y) ← ((¬ X) ∨ Y)
material-implₗ = [∨]-elim ([→]-lift [⊥]-elim) ([→]-intro)
-- ((¬ X) ∨ Y)
-- ((X → ⊥) ∨ Y)
-- ((X → ⊥) ∨ (X → Y))
-- ((X → Y) ∨ (X → Y))
-- (X → Y)

-- This seems to be unprovable in constructive logic
-- material-implᵣ : ∀{X Y : Stmt} → (X → Y) → ((¬ X) ∨ Y)
-- material-implᵣ xy = 
-- (X → Y)
-- ?

-- ??? : ∀{X Y : Stmt} → (X → Y) → (¬ (X ∧ (¬ Y))) -- TODO: This does not work either?
-- (¬ (X ∧ (¬ Y)))
-- ((X ∧ (Y → ⊥)) → ⊥)
-- ?

constructive-dilemma : ∀{A B C D : Stmt} → (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
constructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

-- destructive-dilemma : ∀{A B C D : Stmt} → (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
-- destructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

contrapositiveᵣ : ∀{X Y : Stmt} → (X → Y) → ((¬ X) ← (¬ Y))
contrapositiveᵣ = [→]-syllogism
-- contrapositiveᵣ f ny = ny ∘ f

contrapositive₂ : ∀{X Y : Stmt} → (X → (¬¬ Y)) ← ((¬ X) ← (¬ Y)) -- TODO: At least this works? Or am I missing something?
contrapositive₂ nf x = (swap nf) x
-- (¬ X) ← (¬ Y)
-- (¬ Y) → (¬ X)
-- (Y → ⊥) → (X → ⊥)
-- (Y → ⊥) → X → ⊥
-- X → (Y → ⊥) → ⊥
-- X → ((Y → ⊥) → ⊥)
-- X → (¬ (Y → ⊥))
-- X → (¬ (¬ Y))

contrapositive-variant : ∀{X Y : Stmt} → (X → (¬ Y)) → ((¬ X) ← Y)
contrapositive-variant {X}{Y} = swap

modus-tollens : ∀{X Y : Stmt} → (X → Y) → (¬ Y) → (¬ X)
modus-tollens = contrapositiveᵣ

double-contrapositiveᵣ : ∀{X Y : Stmt} → (X → Y) → ((¬¬ X) → (¬¬ Y))
double-contrapositiveᵣ = contrapositiveᵣ ∘ contrapositiveᵣ

[¬¬]-intro : ∀{X : Stmt} → X → (¬¬ X)
[¬¬]-intro = apply
-- X → (X → ⊥) → ⊥

[¬¬¬]-elim : ∀{X : Stmt} → (¬ (¬ (¬ X))) → (¬ X)
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

[→]ₗ-[¬¬]-elim : ∀{X Y : Stmt} → ((¬¬ X) → Y) → (X → Y)
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

[→][∧]ₗ : ∀{X Y : Stmt} → (X → (¬¬ Y)) ← ¬(X ∧ (¬ Y))
[→][∧]ₗ = Tuple.curry
-- ¬(A ∧ ¬B) → (A → ¬¬B)
--   ¬(A ∧ (¬ B)) //assumption
--   ((A ∧ (B → ⊥)) → ⊥) //Definition: (¬)
--   (A → (B → ⊥) → ⊥) //Tuple.curry
--   (A → ¬(B → ⊥)) //Definition: (¬)
--   (A → ¬(¬ B)) //Definition: (¬)

[→][∧]ᵣ : ∀{X Y : Stmt} → (X → Y) → ¬(X ∧ (¬ Y))
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

[↔]-negative : ∀{X Y} → (X ↔ Y) → ((¬ X) ↔ (¬ Y)) -- TODO: Is the other direction also valid?
[↔]-negative xy = [↔]-intro ([↔]-elimᵣ-[¬] (xy)) ([↔]-elimₗ-[¬] (xy))

[↔]-elim-[∨] : ∀{X Y} → (X ↔ Y) → (X ∨ Y) → (X ∧ Y)
[↔]-elim-[∨] (x↔y) ([∨]-introₗ x) = [∧]-intro x (([↔]-elimᵣ x↔y)(x))
[↔]-elim-[∨] (x↔y) ([∨]-introᵣ y) = [∧]-intro (([↔]-elimₗ x↔y)(y)) y

-- TODO: Is this possible to prove?
-- [↔]-elim-[¬∨¬] : ∀{X Y} → (X ↔ Y) → ((¬ X) ∨ (¬ Y)) → (X ∧ Y)

------------------------------------------
-- Almost-distributivity with duals (De-morgan's laws)

-- [¬][∧]ₗ : ∀{X Y : Stmt} → ((¬ X) ∨ (¬ Y)) ← (¬ (X ∧ Y))
-- [¬][∧]ₗ n = -- TODO: Not possible in constructive logic? Seems to require ¬¬X=X?
-- ((X ∧ Y) → ⊥) → ((X → ⊥) ∨ (Y → ⊥))
-- ¬((X ∧ Y) → ⊥) ← ¬((X → ⊥) ∨ (Y → ⊥))

[¬][∧]ᵣ : ∀{X Y : Stmt} → ((¬ X) ∨ (¬ Y)) → (¬ (X ∧ Y))
[¬][∧]ᵣ ([∨]-introₗ nx) = nx ∘ [∧]-elimₗ
[¬][∧]ᵣ ([∨]-introᵣ ny) = ny ∘ [∧]-elimᵣ
-- (X → ⊥) → (X ∧ Y) → ⊥
-- (Y → ⊥) → (X ∧ Y) → ⊥

[¬][∨] : ∀{X Y : Stmt} → ((¬ X) ∧ (¬ Y)) ↔ (¬ (X ∨ Y))
[¬][∨] = [↔]-intro [¬][∨]₁ [¬][∨]₂
  where [¬][∨]₁ : ∀{X Y : Stmt} → (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
        [¬][∨]₁ f = [∧]-intro (f ∘ [∨]-introₗ) (f ∘ [∨]-introᵣ)
        -- (¬ (X ∨ Y)) → ((¬ X) ∧ (¬ Y))
        -- ((X ∨ Y) → ⊥) → ((X → ⊥) ∧ (Y → ⊥))

        [¬][∨]₂ : ∀{X Y : Stmt} → ((¬ X)∧(¬ Y)) → ¬(X ∨ Y)
        [¬][∨]₂ ([∧]-intro nx ny) = [∨]-elim nx ny
        -- ((¬ X) ∧ (¬ Y)) → (¬ (X ∨ Y))
        -- ((X → ⊥) ∧ (Y → ⊥)) → ((X ∨ Y) → ⊥)
        -- ((X → ⊥) ∧ (Y → ⊥)) → (X ∨ Y) → ⊥
        -- (X → ⊥) → (Y → ⊥) → (X ∨ Y) → ⊥

------------------------------------------
-- Conjunction and implication (Tuples and functions)

[→][∧]-assumption : ∀{X Y Z : Stmt} → ((X ∧ Y) → Z) ↔ (X → Y → Z)
[→][∧]-assumption = [↔]-intro Tuple.uncurry Tuple.curry

[→][∧]-distributivityₗ : ∀{X Y Z : Stmt} → (X → (Y ∧ Z)) ↔ ((X → Y) ∧ (X → Z))
[→][∧]-distributivityₗ = [↔]-intro [→][∧]-distributivityₗ₁ [→][∧]-distributivityₗ₂
  where [→][∧]-distributivityₗ₁ : ∀{X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) → (X → (Y ∧ Z))
        [→][∧]-distributivityₗ₁ ([∧]-intro xy xz) x = [∧]-intro (xy(x)) (xz(x))

        [→][∧]-distributivityₗ₂ : ∀{X Y Z : Stmt} → ((X → Y) ∧ (X → Z)) ← (X → (Y ∧ Z))
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

-- Note:
--   ∀{X} → (X ∨ (¬ X)) ← ((¬¬ X) → X)
--   is not provable because the statement (X ∨ (¬ X)) requires a [¬¬]-elim.
--   TODO: ...I think? I do not think (∀{X} → ¬¬(X ∨ (¬ X)) → ((¬¬ X) ∨ (¬ X))) is provable.
[¬¬]-elim-from-excluded-middle : ∀{X} → (X ∨ (¬ X)) → ((¬¬ X) → X)
[¬¬]-elim-from-excluded-middle ([∨]-introₗ x)  (nnx) = x
[¬¬]-elim-from-excluded-middle ([∨]-introᵣ nx) (nnx) = [⊥]-elim(nnx(nx))

[[¬¬]-elim]-[excluded-middle]-eqₗ : (∀{X} → (¬¬ X) → X) ← (∀{X} → X ∨ (¬ X))
[[¬¬]-elim]-[excluded-middle]-eqₗ or {X} (nnx) with or
... | ([∨]-introₗ x ) = x
... | ([∨]-introᵣ nx) = [⊥]-elim(nnx(nx))

[[¬¬]-elim]-[excluded-middle]-eqᵣ : (∀{X} → (¬¬ X) → X) → (∀{X} → (X ∨ (¬ X)))
[[¬¬]-elim]-[excluded-middle]-eqᵣ (nnxx) = nnxx([¬¬]-excluded-middle)
