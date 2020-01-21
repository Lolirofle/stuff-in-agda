module Logic.Propositional.Theorems where

open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
import      Lvl
open import Type

------------------------------------------
-- Reflexivity

module _ {ℓ} {P : Stmt{ℓ}} where
  [↔]-reflexivity : (P ↔ P)
  [↔]-reflexivity = [↔]-intro id id

  [→]-reflexivity : (P → P)
  [→]-reflexivity = id

------------------------------------------
-- Transitivity

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [→]-transitivity : (P → Q) → (Q → R) → (P → R)
  [→]-transitivity = swap _∘_

  [↔]-transitivity : (P ↔ Q) → (Q ↔ R) → (P ↔ R)
  [↔]-transitivity ([↔]-intro qp pq) ([↔]-intro rq qr) = [↔]-intro (qp ∘ rq) (qr ∘ pq)

  [∧]-transitivity : (P ∧ Q) → (Q ∧ R) → (P ∧ R)
  [∧]-transitivity ([∧]-intro p _) ([∧]-intro _ r) = [∧]-intro p r

------------------------------------------
-- Symmetry

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [∧]-symmetry : (P ∧ Q) → (Q ∧ P)
  [∧]-symmetry = Tuple.swap

  [∨]-symmetry : (P ∨ Q) → (Q ∨ P)
  [∨]-symmetry = Either.swap

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [↔]-symmetry : (P ↔ Q) → (Q ↔ P)
  [↔]-symmetry = [∧]-symmetry

------------------------------------------
-- Operators that implies other ones

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [∧]-to-[↔] : (P ∧ Q) → (P ↔ Q)
  [∧]-to-[↔] ([∧]-intro p q) = [↔]-intro (const p) (const q)

  [∧]-to-[→] : (P ∧ Q) → (P → Q)
  [∧]-to-[→] ([∧]-intro p q) = const q

  [∧]-to-[←] : (P ∧ Q) → (P ← Q)
  [∧]-to-[←] ([∧]-intro p q) = const p

  [∧]-to-[∨] : (P ∧ Q) → (P ∨ Q)
  [∧]-to-[∨] ([∧]-intro p q) = [∨]-introₗ p

  [∨]-to-[←][→] : (P ∨ Q) → (P ← Q)∨(P → Q)
  [∨]-to-[←][→] ([∨]-introₗ p) = [∨]-introₗ (const p)
  [∨]-to-[←][→] ([∨]-introᵣ q) = [∨]-introᵣ (const q)

  -- [↔]-to-[] : ∀{P Q : Stmt} → (P ↔ Q) ← (P ∧ Q) ∨ ((¬ P) ∧ (¬ Q))

  -- TODO: Probably unprovable
  -- [↔]-to-[] : ∀{P Q : Stmt} → (P ↔ Q) → (P ∧ Q) ∨ ((¬ P) ∧ (¬ Q))
  -- [↔]-to-[] ([∧]-intro qp pq) = ?

------------------------------------------
-- Associativity (with respect to ↔)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [∧]-associativity : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
  [∧]-associativity = [↔]-intro [∧]-associativity₁ [∧]-associativity₂
    where [∧]-associativity₁ : ((P ∧ Q) ∧ R) ← (P ∧ (Q ∧ R))
          [∧]-associativity₁ ([∧]-intro p ([∧]-intro q r)) = [∧]-intro ([∧]-intro p q) r

          [∧]-associativity₂ : ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
          [∧]-associativity₂ ([∧]-intro ([∧]-intro p q) r) = [∧]-intro p ([∧]-intro q r)

  [∨]-associativity : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))
  [∨]-associativity = [↔]-intro [∨]-associativity₁ [∨]-associativity₂
    where [∨]-associativity₁ : ((P ∨ Q) ∨ R) ← (P ∨ (Q ∨ R))
          [∨]-associativity₁ ([∨]-introₗ p) = [∨]-introₗ([∨]-introₗ p)
          [∨]-associativity₁ ([∨]-introᵣ([∨]-introₗ q)) = [∨]-introₗ([∨]-introᵣ q)
          [∨]-associativity₁ ([∨]-introᵣ([∨]-introᵣ r)) = [∨]-introᵣ r

          [∨]-associativity₂ : ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))
          [∨]-associativity₂ ([∨]-introₗ([∨]-introₗ p)) = [∨]-introₗ p
          [∨]-associativity₂ ([∨]-introₗ([∨]-introᵣ q)) = [∨]-introᵣ([∨]-introₗ q)
          [∨]-associativity₂ ([∨]-introᵣ r) = [∨]-introᵣ([∨]-introᵣ r)

          -- [∨]-associativity₂ : ∀{P Q R : Stmt} → ((P ∨ Q) ∨ R) ← (P ∨ (Q ∨ R))
          -- [∨]-associativity₂ {P} {Q} {R} stmt = [∨]-associativity₁ {Q} {R} {P} ([∨]-symmetry {P} {Q ∨ R} stmt)

-- TODO: According to https://math.stackexchange.com/questions/440261/associativity-of-iff , this is unprovable
{-[↔]-associativity : ∀{P Q R : Stmt} → ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R))
[↔]-associativity {P}{Q}{R} = [↔]-intro [↔]-associativityₗ [↔]-associativityᵣ where
  [↔]-associativityₗ : ((P ↔ Q) ↔ R) ← (P ↔ (Q ↔ R))
  [↔]-associativityₗ ([↔]-intro yz2x x2yz) = [↔]-intro z2xy xy2z where
    z2xy : (P ↔ Q) ← R
    z2xy r = [↔]-intro y2x x2y where
      y2x : Q → P
      y2x q = yz2x([∧]-to-[↔]([∧]-intro q r))

      x2y : P → Q
      x2y p = [↔]-elimₗ (x2yz(p)) (r)

    xy2z : (P ↔ Q) → R -- TODO: How?
    xy2z ([↔]-intro y2x x2y) = ?

  [↔]-associativityᵣ : ((P ↔ Q) ↔ R) → (P ↔ (Q ↔ R))
  [↔]-associativityᵣ ([↔]-intro z2xy xy2z) = [↔]-intro yz2x x2yz where
    yz2x : P ← (Q ↔ R)
    yz2x ([↔]-intro z2y y2z) = ?

    x2yz : P → (Q ↔ R)
    x2yz p = [↔]-intro z2y y2z where
      z2y : R → Q
      z2y r = [↔]-elimᵣ (z2xy(r)) (p)

      y2z : Q → R
      y2z q = xy2z([∧]-to-[↔]([∧]-intro p q))
-}

------------------------------------------
-- Distributivity

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [∧][∨]-distributivityₗ : (P ∧ (Q ∨ R)) ↔ (P ∧ Q)∨(P ∧ R)
  [∧][∨]-distributivityₗ = [↔]-intro l r where
    l : (P ∧ (Q ∨ R)) ← (P ∧ Q)∨(P ∧ R)
    l([∨]-introₗ ([∧]-intro p q)) = [∧]-intro p ([∨]-introₗ q)
    l([∨]-introᵣ ([∧]-intro p r)) = [∧]-intro p ([∨]-introᵣ r)

    r : (P ∧ (Q ∨ R)) → (P ∧ Q)∨(P ∧ R)
    r([∧]-intro p ([∨]-introₗ q)) = [∨]-introₗ([∧]-intro p q)
    r([∧]-intro p ([∨]-introᵣ r)) = [∨]-introᵣ([∧]-intro p r)

  [∧][∨]-distributivityᵣ : ((P ∨ Q) ∧ R) ↔ (P ∧ R)∨(Q ∧ R)
  [∧][∨]-distributivityᵣ = [↔]-intro l r where
    l : ((P ∨ Q) ∧ R) ← (P ∧ R)∨(Q ∧ R)
    l([∨]-introₗ ([∧]-intro p r)) = [∧]-intro ([∨]-introₗ p) r
    l([∨]-introᵣ ([∧]-intro q r)) = [∧]-intro ([∨]-introᵣ q) r

    r : ((P ∨ Q) ∧ R) → (P ∧ R)∨(Q ∧ R)
    r([∧]-intro ([∨]-introₗ p) r) = [∨]-introₗ([∧]-intro p r)
    r([∧]-intro ([∨]-introᵣ q) r) = [∨]-introᵣ([∧]-intro q r)

  [∨][∧]-distributivityₗ : (P ∨ (Q ∧ R)) ↔ (P ∨ Q)∧(P ∨ R)
  [∨][∧]-distributivityₗ = [↔]-intro l r where
    l : (P ∨ (Q ∧ R)) ← (P ∨ Q)∧(P ∨ R)
    l([∧]-intro ([∨]-introₗ p) ([∨]-introₗ _)) = [∨]-introₗ(p)
    l([∧]-intro ([∨]-introₗ p) ([∨]-introᵣ r)) = [∨]-introₗ(p)
    l([∧]-intro ([∨]-introᵣ q) ([∨]-introₗ p)) = [∨]-introₗ(p)
    l([∧]-intro ([∨]-introᵣ q) ([∨]-introᵣ r)) = [∨]-introᵣ([∧]-intro q r)

    r : (P ∨ (Q ∧ R)) → (P ∨ Q)∧(P ∨ R)
    r([∨]-introₗ p)               = [∧]-intro ([∨]-introₗ p) ([∨]-introₗ p)
    r([∨]-introᵣ ([∧]-intro q r)) = [∧]-intro ([∨]-introᵣ q) ([∨]-introᵣ r)

  [∨][∧]-distributivityᵣ : ((P ∧ Q) ∨ R) ↔ (P ∨ R)∧(Q ∨ R)
  [∨][∧]-distributivityᵣ = [↔]-intro l r where
    l : ((P ∧ Q) ∨ R) ← (P ∨ R)∧(Q ∨ R)
    l([∧]-intro ([∨]-introₗ p) ([∨]-introₗ q)) = [∨]-introₗ([∧]-intro p q)
    l([∧]-intro ([∨]-introₗ p) ([∨]-introᵣ r)) = [∨]-introᵣ(r)
    l([∧]-intro ([∨]-introᵣ r) ([∨]-introₗ q)) = [∨]-introᵣ(r)
    l([∧]-intro ([∨]-introᵣ r) ([∨]-introᵣ _)) = [∨]-introᵣ(r)

    r : ((P ∧ Q) ∨ R) → (P ∨ R)∧(Q ∨ R)
    r([∨]-introₗ ([∧]-intro p q)) = [∧]-intro ([∨]-introₗ p) ([∨]-introₗ q)
    r([∨]-introᵣ r)               = [∧]-intro ([∨]-introᵣ r) ([∨]-introᵣ r)

------------------------------------------
-- Identity (with respect to ↔) (TODO: Looks like → rather than ↔)

module _ {ℓ} {P : Stmt{ℓ}} where
  [∧]-identityₗ : (⊤ ∧ P) → P
  [∧]-identityₗ ([∧]-intro _ p) = p

  [∧]-identityᵣ : (P ∧ ⊤) → P
  [∧]-identityᵣ ([∧]-intro p _) = p

  [∨]-identityₗ : (⊥ ∨ P) → P
  [∨]-identityₗ ([∨]-introₗ ())
  [∨]-identityₗ ([∨]-introᵣ p) = p

  [∨]-identityᵣ : (P ∨ ⊥) → P
  [∨]-identityᵣ ([∨]-introₗ p) = p
  [∨]-identityᵣ ([∨]-introᵣ ())

  [→]-identityₗ : (⊤ → P) → P
  [→]-identityₗ f = f([⊤]-intro)

  [∧]-nullifierₗ : (⊥ ∧ P) → ⊥
  [∧]-nullifierₗ ([∧]-intro () _)

  [∧]-nullifierᵣ : (P ∧ ⊥) → ⊥
  [∧]-nullifierᵣ ([∧]-intro _ ())

module _ {ℓ₂}{ℓ₃} {_▫_ : Stmt{Lvl.𝟎} → Stmt{ℓ₂} → Stmt{ℓ₃}} where
  [⊤]-as-nullifierₗ : ∀{P : Stmt} → (⊤ ▫ P) → ⊤
  [⊤]-as-nullifierₗ _ = [⊤]-intro

module _ {ℓ₁}{ℓ₃} {_▫_ : Stmt{ℓ₁} → Stmt{Lvl.𝟎} → Stmt{ℓ₃}} where
  [⊤]-as-nullifierᵣ : ∀{P : Stmt} → (P ▫ ⊤) → ⊤
  [⊤]-as-nullifierᵣ _ = [⊤]-intro

------------------------------------------
-- Syllogism

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [∨]-syllogismₗ : (P ∨ Q) → (¬ P) → Q
  [∨]-syllogismₗ ([∨]-introₗ p) np = [⊥]-elim(np p)
  [∨]-syllogismₗ ([∨]-introᵣ q) = const q

  [∨]-syllogismᵣ : (P ∨ Q) → (¬ Q) → P
  [∨]-syllogismᵣ ([∨]-introₗ p) = const p
  [∨]-syllogismᵣ ([∨]-introᵣ q) nq = [⊥]-elim(nq q)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [→]-syllogism : (P → Q) → (Q → R) → (P → R)
  [→]-syllogism = liftᵣ

------------------------------------------
-- Other

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{T : Stmt{ℓ₃}} where
  [→]-lift : (P → Q) → ((T → P) → (T → Q))
  [→]-lift = liftₗ

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {A : Stmt{ℓ₁}}{B : Stmt{ℓ₂}}{C : Stmt{ℓ₃}}{D : Stmt{ℓ₄}} where
  constructive-dilemma : (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
  constructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

  -- destructive-dilemma : (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
  -- destructive-dilemma l r = [∨]-elim ([∨]-introₗ ∘ l) ([∨]-introᵣ ∘ r)

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  contrapositiveᵣ : (P → Q) → ((¬ P) ← (¬ Q))
  contrapositiveᵣ = swap _∘_

  contrapositive-variantᵣ : (P → (¬ Q)) → ((¬ P) ← Q)
  contrapositive-variantᵣ = swap

  modus-tollens : (P → Q) → (¬ Q) → (¬ P)
  modus-tollens = contrapositiveᵣ

module _ {ℓ} {P : Stmt{ℓ}} where
  [¬¬]-intro : P → (¬¬ P)
  [¬¬]-intro = apply
    -- P → (P → ⊥) → ⊥

  [¬¬¬]-elim : (¬ (¬ (¬ P))) → (¬ P)
  [¬¬¬]-elim = contrapositiveᵣ [¬¬]-intro
    -- (((P → ⊥) → ⊥) → ⊥) → (P → ⊥)
    -- (((P → ⊥) → ⊥) → ⊥) → P → ⊥
    --   (A → B) → ((B → ⊥) → (A → ⊥)) //contrapositiveᵣ
    --   (A → B) → (B → ⊥) → (A → ⊥)
    --   (A → B) → (B → ⊥) → A → ⊥
    --   (P → ((P → ⊥) → ⊥)) → (((P → ⊥) → ⊥) → ⊥) → P → ⊥ //A≔P , B≔((P → ⊥) → ⊥)

    --   P → (¬ (¬ P)) //[¬¬]-intro
    --   P → ((P → ⊥) → ⊥)

    --   (((P → ⊥) → ⊥) → ⊥) → P → ⊥ //[→]-elim (Combining those two)
    --   (((P → ⊥) → ⊥) → ⊥) → (P → ⊥)

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [→][∧]ᵣ : (P → Q) → ¬(P ∧ (¬ Q))
  [→][∧]ᵣ f = Tuple.uncurry([¬¬]-intro ∘ f)

  [¬→][∧]ₗ : ¬(P → Q) ← (P ∧ (¬ Q))
  [¬→][∧]ₗ (pnq) = contrapositiveᵣ([→][∧]ᵣ)([¬¬]-intro pnq)

  -- [→][¬∧] : (P → ¬ Q) ↔ ¬(P ∧ Q) -- TODO: Probably needs [¬¬]-elim

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [↔]-of-[∧] : ((P ∧ R) ↔ (Q ∧ R)) → (R → (P ↔ Q))
  [↔]-of-[∧] ([↔]-intro qrpr prqr) r =
    ([↔]-intro
      (q ↦ [∧]-elimₗ(qrpr([∧]-intro q r)))
      (p ↦ [∧]-elimₗ(prqr([∧]-intro p r)))
    )

  [↔]-adding-[∧] : (P ↔ Q) → ((P ∧ R) ↔ (Q ∧ R))
  [↔]-adding-[∧] ([↔]-intro qp pq) =
    ([↔]-intro
      (qr ↦ [∧]-intro (qp([∧]-elimₗ qr)) ([∧]-elimᵣ qr))
      (pr ↦ [∧]-intro (pq([∧]-elimₗ pr)) ([∧]-elimᵣ pr))
    )

module _ {ℓ} {P : Stmt{ℓ}}{Q : Stmt{ℓ}} where
  [↔]-elimₗ-[¬] : (P ↔ Q) → (¬ P) → (¬ Q)
  [↔]-elimₗ-[¬] pq np q = np([↔]-elimₗ(q)(pq))

  [↔]-elimᵣ-[¬] : (P ↔ Q) → (¬ Q) → (¬ P)
  [↔]-elimᵣ-[¬] pq nq p = nq([↔]-elimᵣ(p)(pq))

  [↔]-negationᵣ : (P ↔ Q) → ((¬ P) ↔ (¬ Q)) -- TODO: Is the other direction also valid? Probably not
  [↔]-negationᵣ pq = [↔]-intro ([↔]-elimᵣ-[¬] (pq)) ([↔]-elimₗ-[¬] (pq))

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [↔]-elim-[∨] : (P ↔ Q) → (P ∨ Q) → (P ∧ Q)
  [↔]-elim-[∨] (p↔q) ([∨]-introₗ p) = [∧]-intro p ([↔]-elimᵣ(p) p↔q)
  [↔]-elim-[∨] (p↔q) ([∨]-introᵣ q) = [∧]-intro ([↔]-elimₗ(q) p↔q) q

  -- TODO: Is this possible to prove?
  -- [↔]-elim-[¬∨¬] : (P ↔ Q) → ((¬ P) ∨ (¬ Q)) → (P ∧ Q)

------------------------------------------
-- Almost-distributivity with duals (De-morgan's laws)

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [¬][∧]ᵣ : ((¬ P) ∨ (¬ Q)) → (¬ (P ∧ Q))
  [¬][∧]ᵣ ([∨]-introₗ np) = np ∘ [∧]-elimₗ
  [¬][∧]ᵣ ([∨]-introᵣ nq) = nq ∘ [∧]-elimᵣ
  -- (P → ⊥) → (P ∧ Q) → ⊥
  -- (Q → ⊥) → (P ∧ Q) → ⊥

  [¬][∨] : ((¬ P) ∧ (¬ Q)) ↔ (¬ (P ∨ Q))
  [¬][∨] = [↔]-intro [¬][∨]₁ [¬][∨]₂
    where [¬][∨]₁ : (¬ (P ∨ Q)) → ((¬ P) ∧ (¬ Q))
          [¬][∨]₁ f = [∧]-intro (f ∘ [∨]-introₗ) (f ∘ [∨]-introᵣ)
          -- (¬ (P ∨ Q)) → ((¬ P) ∧ (¬ Q))
          -- ((P ∨ Q) → ⊥) → ((P → ⊥) ∧ (Q → ⊥))

          [¬][∨]₂ : ((¬ P)∧(¬ Q)) → ¬(P ∨ Q)
          [¬][∨]₂ ([∧]-intro np nq) = [∨]-elim np nq
          -- ((¬ P) ∧ (¬ Q)) → (¬ (P ∨ Q))
          -- ((P → ⊥) ∧ (Q → ⊥)) → ((P ∨ Q) → ⊥)
          -- ((P → ⊥) ∧ (Q → ⊥)) → (P ∨ Q) → ⊥
          -- (P → ⊥) → (Q → ⊥) → (P ∨ Q) → ⊥

------------------------------------------
-- Conjunction and implication (Tuples and functions)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [→][∧]-assumption : ((P ∧ Q) → R) ↔ (P → Q → R)
  [→][∧]-assumption = [↔]-intro Tuple.uncurry Tuple.curry

  [→][∧]-distributivityₗ : (P → (Q ∧ R)) ↔ ((P → Q) ∧ (P → R))
  [→][∧]-distributivityₗ = [↔]-intro l r
    where l : ((P → Q) ∧ (P → R)) → (P → (Q ∧ R))
          l ([∧]-intro pq pr) p = [∧]-intro (pq(p)) (pr(p))

          r : ((P → Q) ∧ (P → R)) ← (P → (Q ∧ R))
          r both = [∧]-intro ([∧]-elimₗ ∘ both) ([∧]-elimᵣ ∘ both)

  [→][∨]-distributivityₗ : (P → (Q ∨ R)) ← ((P → Q) ∨ (P → R))
  [→][∨]-distributivityₗ = l -- [↔]-intro l r
    where l : ((P → Q) ∨ (P → R)) → (P → (Q ∨ R))
          l ([∨]-introₗ pq) p = [∨]-introₗ (pq(p))
          l ([∨]-introᵣ pr) p = [∨]-introᵣ (pr(p))

          -- r : ∀{P Q R : Stmt} → ((P → Q) ∨ (P → R)) ← (P → (Q ∨ R))
          -- r both = [∨]-introₗ (p ↦ both p)

module _ {ℓ} {P : Stmt{ℓ}} where
  non-contradiction : ¬(P ∧ (¬ P))
  non-contradiction(p , np) = np p

------------------------------------------
-- Redundant formulas in operations

module _ {ℓ₁}{ℓ₂} {A : Stmt{ℓ₁}}{B : Stmt{ℓ₂}} where
  [→]-redundancy : (A → A → B) → (A → B)
  [→]-redundancy(f)(a) = f(a)(a)

module _ {ℓ} {A : Stmt{ℓ}} where
  [∧]-redundancy : (A ∧ A) ↔ A
  [∧]-redundancy = [↔]-intro (p ↦ [∧]-intro(p)(p)) [∧]-elimₗ

  [∨]-redundancy : (A ∨ A) ↔ A
  [∨]-redundancy = [↔]-intro [∨]-introₗ (p ↦ [∨]-elim id id p)

------------------------------------------
-- Disjunctive normal form conversions in classical logic

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  -- Also called: Material implication
  [→]-disjunctive-formₗ : (P → Q) ← ((¬ P) ∨ Q)
  [→]-disjunctive-formₗ = [∨]-elim ([→]-lift [⊥]-elim) (const)
  -- ((¬ P) ∨ Q)
  -- ((P → ⊥) ∨ Q)
  -- ((P → ⊥) ∨ (P → Q))
  -- ((P → Q) ∨ (P → Q))
  -- (P → Q)

  [↔]-disjunctive-formₗ : (P ↔ Q) ← ((P ∧ Q) ∨ ((¬ P) ∧ (¬ Q)))
  [↔]-disjunctive-formₗ ([∨]-introₗ ([∧]-intro p q))   = [↔]-intro (const p) (const q)
  [↔]-disjunctive-formₗ ([∨]-introᵣ ([∧]-intro np nq)) = [↔]-intro ([⊥]-elim ∘ nq) ([⊥]-elim ∘ np)

  -- TODO: Probably unprovable
  -- [↔]-disjunctive-formᵣ : ∀{P Q : Stmt} → (P ↔ Q) → ((P ∧ Q) ∨ ((¬ P) ∧ (¬ Q)))
  -- [↔]-disjunctive-formᵣ ([↔]-intro qp pq) = 

------------------------------------------
-- Conjuctive normal form conversions in classical logic

-- TODO: None of them are provable?
-- [↔]-conjunctive-form : ∀{P Q : Stmt} → (P ↔ Q) ↔ ((P ∨ Q) ∧ ((¬ P) ∨ (¬ Q)))
-- [↔]-conjunctive-form ([↔]-intro qp pq) = [∨]-elim ([→]-lift [⊥]-elim) (const)

------------------------------------------
-- Stuff related to classical logic

module _ {ℓ} {P : Stmt{ℓ}} where
  [¬¬]-excluded-middle : ¬¬(P ∨ (¬ P))
  [¬¬]-excluded-middle =
    ([¬]-intro(naorna ↦
      ((non-contradiction([∧]-intro
        (([∨]-introᵣ
          (([¬]-intro(a ↦
            ((non-contradiction([∧]-intro
              (([∨]-introₗ a) :of:  (P ∨ (¬ P)))
              (naorna         :of: ¬(P ∨ (¬ P)))
            )) :of: ⊥)
          )) :of: (¬ P))
        ) :of: (P ∨ (¬ P)))
        (naorna :of: ¬(P ∨ (¬ P)))
      )) :of: ⊥)
    )) :of: ¬¬(P ∨ (¬ P))

  -- Note:
  --   ∀{P} → (P ∨ (¬ P)) ← ((¬¬ P) → P)
  --   is not provable because the statement (P ∨ (¬ P)) requires a [¬¬]-elim.
  --   TODO: ...I think? I do not think (∀{P} → ¬¬(P ∨ (¬ P)) → ((¬¬ P) ∨ (¬ P))) is provable.
  [¬¬]-elim-from-excluded-middle : (P ∨ (¬ P)) → ((¬¬ P) → P)
  [¬¬]-elim-from-excluded-middle ([∨]-introₗ p)  (nnp) = p
  [¬¬]-elim-from-excluded-middle ([∨]-introᵣ np) (nnp) = [⊥]-elim(nnp(np))

  [¬¬]-elim-from-callcc : (∀{Q : Stmt{Lvl.𝟎}} → (((P → Q) → P) → P)) → ((¬¬ P) → P)
  [¬¬]-elim-from-callcc (callcc) (nnp) = callcc{⊥} ([⊥]-elim ∘ nnp)

module _ {ℓ} where
  [[¬¬]-elim]-[excluded-middle]-eqₗ : (∀{P : Stmt{ℓ}} → (¬¬ P) → P) ←ᶠ (∀{P : Stmt{ℓ}} → (P ∨ (¬ P)))
  [[¬¬]-elim]-[excluded-middle]-eqₗ or {P} (nnp) with or
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = [⊥]-elim(nnp(np))

  [[¬¬]-elim]-[excluded-middle]-eqᵣ : (∀{P : Stmt{ℓ}} → (¬¬ P) → P) → (∀{P : Stmt{ℓ}} → (P ∨ (¬ P)))
  [[¬¬]-elim]-[excluded-middle]-eqᵣ (nnpp) = nnpp([¬¬]-excluded-middle)

  -- TODO: https://math.stackexchange.com/questions/910240/equivalence-between-middle-excluded-law-and-double-negation-elimination-in-heyti

  [callcc]-[[¬¬]-elim]-eqₗ : (∀{P : Stmt{ℓ}}{Q : Stmt{Lvl.𝟎}} → (((P → Q) → P) → P)) → (∀{P} → (¬¬ P) → P)
  [callcc]-[[¬¬]-elim]-eqₗ (callcc) {P} (nnp) = callcc{P}{⊥} (np ↦ [⊥]-elim(nnp(np)))

  [callcc]-[[¬¬]-elim]-eqᵣ : (∀{P : Stmt{ℓ}} → (¬¬ P) → P) → (∀{P Q : Stmt{ℓ}} → (((P → Q) → P) → P))
  [callcc]-[[¬¬]-elim]-eqᵣ (nnpp) {P}{Q} (pqp) = nnpp([¬]-intro(np ↦ np(pqp(p ↦ [⊥]-elim(np p)))))

  [callcc]-[excluded-middle]-eqₗ : (∀{P : Stmt{ℓ}} → (P ∨ (¬ P))) → (∀{P Q : Stmt{ℓ}} → (((P → Q) → P) → P))
  [callcc]-[excluded-middle]-eqₗ or {P}{Q} (pqp) with or
  ... | ([∨]-introₗ p ) = p
  ... | ([∨]-introᵣ np) = pqp([⊥]-elim ∘ np)

  [callcc]-[excluded-middle]-eqᵣ : (∀{P : Stmt{ℓ}}{Q : Stmt{Lvl.𝟎}} → (((P → Q) → P) → P)) → (∀{P : Stmt{ℓ}} → (P ∨ (¬ P)))
  [callcc]-[excluded-middle]-eqᵣ (callcc) {P} = callcc{P ∨ (¬ P)}{⊥} (nor ↦ [⊥]-elim ([¬¬]-excluded-middle (nor)))

------------------------------------------
-- XOR

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [⊕][↔]-contradiction : (P ⊕ Q) → (P ↔ Q) → ⊥
  [⊕][↔]-contradiction ([⊕]-introₗ p nq) pq = nq([↔]-elimᵣ p pq)
  [⊕][↔]-contradiction ([⊕]-introᵣ q np) pq = np([↔]-elimₗ q pq)

  [⊕]-to-[∨] : (P ⊕ Q) → (P ∨ Q)
  [⊕]-to-[∨] ([⊕]-introₗ p _) = [∨]-introₗ p
  [⊕]-to-[∨] ([⊕]-introᵣ q _) = [∨]-introᵣ q

  [⊕]-to-[¬∨] : (P ⊕ Q) → ((¬ P) ∨ (¬ Q))
  [⊕]-to-[¬∨] ([⊕]-introₗ _ nq) = [∨]-introᵣ nq
  [⊕]-to-[¬∨] ([⊕]-introᵣ _ np) = [∨]-introₗ np

  [⊕]-excluded-middleₗ : (P ⊕ Q) → (P ∨ (¬ P))
  [⊕]-excluded-middleₗ ([⊕]-introₗ p nq) = [∨]-introₗ p
  [⊕]-excluded-middleₗ ([⊕]-introᵣ q np) = [∨]-introᵣ np

  [⊕]-excluded-middleᵣ : (P ⊕ Q) → (Q ∨ (¬ Q))
  [⊕]-excluded-middleᵣ ([⊕]-introₗ p nq) = [∨]-introᵣ nq
  [⊕]-excluded-middleᵣ ([⊕]-introᵣ q np) = [∨]-introₗ q
