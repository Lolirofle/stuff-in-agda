module Logic.Propositional.Theorems where

import      BidirectionalFunction
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Function
open import Functional
open import Logic
open import Logic.Propositional
import      Lvl
open import Syntax.Type
open import Type

------------------------------------------
-- Reflexivity

module _ {ℓ} {P : Stmt{ℓ}} where
  [↔]-reflexivity : (P ↔ P)
  [↔]-reflexivity = BidirectionalFunction.id

  [→]-reflexivity : (P → P)
  [→]-reflexivity = id

------------------------------------------
-- Transitivity

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [→]-transitivity : (P → Q) → (Q → R) → (P → R)
  [→]-transitivity = liftᵣ

  [↔]-transitivity : (P ↔ Q) → (Q ↔ R) → (P ↔ R)
  [↔]-transitivity pq qr = BidirectionalFunction.map pq BidirectionalFunction.id BidirectionalFunction.$ₗ qr

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
  [↔]-symmetry = BidirectionalFunction.rev BidirectionalFunction.$ᵣ_

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

  [¬∧¬]-to-[↔] : ((¬ P) ∧ (¬ Q)) → (P ↔ Q)
  [¬∧¬]-to-[↔] ([∧]-intro np nq) = [↔]-intro ([⊥]-elim ∘ nq) ([⊥]-elim ∘ np)

------------------------------------------
-- Associativity (with respect to ↔)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [∧]-associativity : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
  [∧]-associativity = [↔]-intro Tuple.associateLeft Tuple.associateRight

  [∨]-associativity : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))
  [∨]-associativity = [↔]-intro Either.associateLeft Either.associateRight

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
-- Identity (with respect to →)

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
-- Other

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [∨]-not-left : (P ∨ Q) → (¬ P) → Q
  [∨]-not-left ([∨]-introₗ p) np = [⊥]-elim(np p)
  [∨]-not-left ([∨]-introᵣ q) = const q

  [∨]-not-right : (P ∨ Q) → (¬ Q) → P
  [∨]-not-right ([∨]-introₗ p) = const p
  [∨]-not-right ([∨]-introᵣ q) nq = [⊥]-elim(nq q)

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{T : Stmt{ℓ₃}} where
  [→]-lift : (P → Q) → ((T → P) → (T → Q))
  [→]-lift = liftₗ

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  contrapositiveᵣ : (P → Q) → ((¬ P) ← (¬ Q))
  contrapositiveᵣ = [→]-transitivity

  contrapositive-variant : (P → (¬ Q)) ↔ ((¬ P) ← Q)
  contrapositive-variant = [↔]-intro swap swap

  modus-tollens : (P → Q) → (¬ Q) → (¬ P)
  modus-tollens = contrapositiveᵣ

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {A : Stmt{ℓ₁}}{B : Stmt{ℓ₂}}{C : Stmt{ℓ₃}}{D : Stmt{ℓ₄}} where
  constructive-dilemma : (A → B) → (C → D) → (A ∨ C) → (B ∨ D)
  constructive-dilemma = [∨]-elim2

  destructive-dilemma : (A → B) → (C → D) → ((¬ B) ∨ (¬ D)) → ((¬ A) ∨ (¬ C))
  destructive-dilemma l r = [∨]-elim2 (contrapositiveᵣ l) (contrapositiveᵣ r)

module _ {ℓ} {P : Stmt{ℓ}} where
  [¬¬]-intro : P → (¬¬ P)
  [¬¬]-intro = apply
    -- P → (P → ⊥) → ⊥

  [¬¬¬]-elim : (¬ (¬ (¬ P))) → (¬ P)
  [¬¬¬]-elim = contrapositiveᵣ [¬¬]-intro

module _ {ℓ₁}{ℓ₂}{ℓ₃} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}}{R : Stmt{ℓ₃}} where
  [↔]-move-out-[∧]ᵣ : ((P ∧ R) ↔ (Q ∧ R)) → (R → (P ↔ Q))
  [↔]-move-out-[∧]ᵣ ([↔]-intro qrpr prqr) r =
    ([↔]-intro
      (q ↦ [∧]-elimₗ(qrpr([∧]-intro q r)))
      (p ↦ [∧]-elimₗ(prqr([∧]-intro p r)))
    )

  [∧]-unaryOperatorₗ : (P ↔ Q) → ((P ∧ R) ↔ (Q ∧ R))
  [∧]-unaryOperatorₗ ([↔]-intro qp pq) =
    ([↔]-intro
      (qr ↦ [∧]-intro (qp([∧]-elimₗ qr)) ([∧]-elimᵣ qr))
      (pr ↦ [∧]-intro (pq([∧]-elimₗ pr)) ([∧]-elimᵣ pr))
    )

  currying : (P → (Q → R)) ↔ ((P ∧ Q) → R)
  currying = [↔]-intro Tuple.curry Tuple.uncurry

module _ {ℓ₁}{ℓ₂}{ℓ₃}{ℓ₄} {A : Stmt{ℓ₁}}{B : Stmt{ℓ₂}}{C : Stmt{ℓ₃}}{D : Stmt{ℓ₄}} where
  [∧]-binaryOperator : (A ↔ C) → (B ↔ D) → ((A ∧ B) ↔ (C ∧ D))
  [∧]-binaryOperator ([↔]-intro ca ac) ([↔]-intro db bd) = [↔]-intro (Tuple.map ca db) (Tuple.map ac bd)

  [∨]-binaryOperator : (A ↔ C) → (B ↔ D) → ((A ∨ B) ↔ (C ∨ D))
  [∨]-binaryOperator ([↔]-intro ca ac) ([↔]-intro db bd) = [↔]-intro (Either.map ca db) (Either.map ac bd)

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [↔]-not-left : (P ↔ Q) → (¬ P) → (¬ Q)
  [↔]-not-left pq np q = np([↔]-elimₗ(q)(pq))

  [↔]-not-right : (P ↔ Q) → (¬ Q) → (¬ P)
  [↔]-not-right pq nq p = nq([↔]-elimᵣ(p)(pq))

  [¬]-unaryOperator : (P ↔ Q) → ((¬ P) ↔ (¬ Q))
  [¬]-unaryOperator pq = [↔]-intro ([↔]-not-right (pq)) ([↔]-not-left (pq))

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [↔]-elim-[∨] : (P ↔ Q) → (P ∨ Q) → (P ∧ Q)
  [↔]-elim-[∨] (p↔q) ([∨]-introₗ p) = [∧]-intro p ([↔]-elimᵣ(p) p↔q)
  [↔]-elim-[∨] (p↔q) ([∨]-introᵣ q) = [∧]-intro ([↔]-elimₗ(q) p↔q) q

module _ {ℓ} {P : Stmt{ℓ}} where
  provable-top-equivalence : P → (P ↔ ⊤)
  provable-top-equivalence p = [↔]-intro (const p) (const [⊤]-intro)

  unprovable-bottom-equivalence : (¬ P) → (P ↔ ⊥)
  unprovable-bottom-equivalence np = [↔]-intro [⊥]-elim np

------------------------------------------
-- Negation is almost preserved over the conjunction-dijunction dual (De-morgan's laws).

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [¬]-preserves-[∧][∨]ₗ : (¬ (P ∧ Q)) ← ((¬ P) ∨ (¬ Q))
  [¬]-preserves-[∧][∨]ₗ = [∨]-elim (_∘ [∧]-elimₗ) (_∘ [∧]-elimᵣ)

  [¬]-preserves-[∨][∧] : (¬ (P ∨ Q)) ↔ ((¬ P) ∧ (¬ Q))
  [¬]-preserves-[∨][∧] = [↔]-intro
    (Tuple.elim [∨]-elim)
    (f ↦ [∧]-intro (f ∘ [∨]-introₗ) (f ∘ [∨]-introᵣ))

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

  [→][∨]-distributivityₗₗ : (P → (Q ∨ R)) ← ((P → Q) ∨ (P → R))
  [→][∨]-distributivityₗₗ = l
    where l : ((P → Q) ∨ (P → R)) → (P → (Q ∨ R))
          l ([∨]-introₗ pq) p = [∨]-introₗ (pq(p))
          l ([∨]-introᵣ pr) p = [∨]-introᵣ (pr(p))

  [→ₗ][∨][∧]-preserving : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R))
  [→ₗ][∨][∧]-preserving = [↔]-intro l r where
    l : ((P ∨ Q) → R) ← ((P → R) ∧ (Q → R))
    l ([∧]-intro pr qr) ([∨]-introₗ p) = pr p
    l ([∧]-intro pr qr) ([∨]-introᵣ q) = qr q

    r : ((P ∨ Q) → R) → ((P → R) ∧ (Q → R))
    r pqr = [∧]-intro (pqr ∘ [∨]-introₗ) (pqr ∘ [∨]-introᵣ)

module _ {ℓ} {P : Stmt{ℓ}} where
  non-contradiction : ¬(P ∧ (¬ P))
  non-contradiction(p , np) = np p

------------------------------------------
-- Redundant formulas in operations

module _ {ℓ₁}{ℓ₂} {A : Stmt{ℓ₁}}{B : Stmt{ℓ₂}} where
  [→]-redundancy : (A → A → B) → (A → B)
  [→]-redundancy = _$₂_

module _ {ℓ} {A : Stmt{ℓ}} where
  [∧]-redundancy : (A ∧ A) ↔ A
  [∧]-redundancy = [↔]-intro ([∧]-intro $₂_) [∧]-elimₗ

  [∨]-redundancy : (A ∨ A) ↔ A
  [∨]-redundancy = [↔]-intro [∨]-introₗ ([∨]-elim id id)

------------------------------------------
-- Disjunctive forms

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  -- Also called: Material implication
  [→]-disjunctive-formₗ : (P → Q) ← ((¬ P) ∨ Q)
  [→]-disjunctive-formₗ = [∨]-elim ([→]-lift [⊥]-elim) const

  [↔]-disjunctive-formₗ : (P ↔ Q) ← ((P ∧ Q) ∨ ((¬ P) ∧ (¬ Q)))
  [↔]-disjunctive-formₗ ([∨]-introₗ pq)   = [∧]-to-[↔] pq
  [↔]-disjunctive-formₗ ([∨]-introᵣ npnq) = Tuple.map ([⊥]-elim ∘_) ([⊥]-elim ∘_) (Tuple.swap npnq)

  -- TODO: Probably unprovable
  -- [↔]-disjunctive-formᵣ : ∀{P Q : Stmt} → (P ↔ Q) → ((P ∧ Q) ∨ ((¬ P) ∧ (¬ Q)))
  -- [↔]-disjunctive-formᵣ ([↔]-intro qp pq) = 

  [¬→]-disjunctive-formₗ : ((¬ P) → Q) ← (P ∨ Q)
  [¬→]-disjunctive-formₗ = [∨]-not-left

------------------------------------------
-- Conjuctive forms

-- TODO: None of them are provable?
-- [↔]-conjunctive-form : ∀{P Q : Stmt} → (P ↔ Q) ↔ ((P ∨ Q) ∧ ((¬ P) ∨ (¬ Q)))
-- [↔]-conjunctive-form ([↔]-intro qp pq) = [∨]-elim ([→]-lift [⊥]-elim) (const)

module _ {ℓ₁ ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [→][∧]ᵣ : (P → Q) → ¬(P ∧ (¬ Q))
  [→][∧]ᵣ f = Tuple.uncurry([¬¬]-intro ∘ f)

  [¬→][∧]ₗ : ¬(P → Q) ← (P ∧ (¬ Q))
  [¬→][∧]ₗ = swap [→][∧]ᵣ

  [→¬]-¬[∧] : (P → (¬ Q)) ↔ ¬(P ∧ Q)
  [→¬]-¬[∧] = currying

------------------------------------------
-- Equivalences (TODO: I remember these being defined somewhere else, but I am not sure. At least some special cases have been used somewhere else)

module _ where
  private variable ℓ : Lvl.Level
  private variable A A₁ A₂ B B₁ B₂ : Type{ℓ}

  [∧]-map-[↔] : (A₁ ↔ A₂) → (B₁ ↔ B₂) → ((A₁ ∧ B₁) ↔ (A₂ ∧ B₂))
  [∧]-map-[↔] a b = [↔]-intro (Tuple.map ([↔]-to-[←] a) ([↔]-to-[←] b)) (Tuple.map ([↔]-to-[→] a) ([↔]-to-[→] b))

  [∧]-mapₗ-[↔] : (A₁ ↔ A₂) → ((A₁ ∧ B) ↔ (A₂ ∧ B))
  [∧]-mapₗ-[↔] a = [∧]-map-[↔] a [↔]-reflexivity

  [∧]-mapᵣ-[↔] : (B₁ ↔ B₂) → ((A ∧ B₁) ↔ (A ∧ B₂))
  [∧]-mapᵣ-[↔] b = [∧]-map-[↔] [↔]-reflexivity b

  [∨]-map-[↔] : (A₁ ↔ A₂) → (B₁ ↔ B₂) → ((A₁ ∨ B₁) ↔ (A₂ ∨ B₂))
  [∨]-map-[↔] a b = [↔]-intro (Either.map ([↔]-to-[←] a) ([↔]-to-[←] b)) (Either.map ([↔]-to-[→] a) ([↔]-to-[→] b))

  [∨]-mapₗ-[↔] : (A₁ ↔ A₂) → ((A₁ ∨ B) ↔ (A₂ ∨ B))
  [∨]-mapₗ-[↔] a = [∨]-map-[↔] a [↔]-reflexivity

  [∨]-mapᵣ-[↔] : (B₁ ↔ B₂) → ((A ∨ B₁) ↔ (A ∨ B₂))
  [∨]-mapᵣ-[↔] b = [∨]-map-[↔] [↔]-reflexivity b

  [↔]-map-[↔] : (A₁ ↔ A₂) → (B₁ ↔ B₂) → ((A₁ ↔ B₁) ↔ (A₂ ↔ B₂))
  [↔]-map-[↔] a b =
    [↔]-intro
      (Tuple.map
        (b₂a₂ ↦ [↔]-to-[←] a ∘ b₂a₂ ∘ [↔]-to-[→] b)
        (a₂b₂ ↦ [↔]-to-[←] b ∘ a₂b₂ ∘ [↔]-to-[→] a)
      )
      (Tuple.map
        (b₁a₁ ↦ [↔]-to-[→] a ∘ b₁a₁ ∘ [↔]-to-[←] b)
        (a₁b₁ ↦ [↔]-to-[→] b ∘ a₁b₁ ∘ [↔]-to-[←] a)
      )

  [↔]-mapₗ-[↔] : (A₁ ↔ A₂) → ((A₁ ↔ B) ↔ (A₂ ↔ B))
  [↔]-mapₗ-[↔] a = [↔]-map-[↔] a [↔]-reflexivity

  [↔]-mapᵣ-[↔] : (B₁ ↔ B₂) → ((A ↔ B₁) ↔ (A ↔ B₂))
  [↔]-mapᵣ-[↔] b = [↔]-map-[↔] [↔]-reflexivity b

  [→]-map-[↔] : (A₁ ↔ A₂) → (B₁ ↔ B₂) → ((A₁ → B₁) ↔ (A₂ → B₂))
  [→]-map-[↔] a b = [↔]-intro (ab ↦ [↔]-to-[←] b ∘ ab ∘ [↔]-to-[→] a) (ab ↦ [↔]-to-[→] b ∘ ab ∘ [↔]-to-[←] a)

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

  -- TODO: Does not have to be over all propositions P in assumption. Only wem P and wem Q are used.
  weak-excluded-middle-[¬][∧]ₗ : (∀{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P)) ↔ (∀{P : Stmt{ℓ}}{Q : Stmt{ℓ}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q)))
  weak-excluded-middle-[¬][∧]ₗ = [↔]-intro l r where
    l : (∀{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P)) ← (∀{P : Stmt{ℓ}}{Q : Stmt{ℓ}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q)))
    l [¬][∧]ₗ = [¬][∧]ₗ non-contradiction

    r : (∀{P : Stmt{ℓ}} → (¬ P) ∨ (¬¬ P)) → (∀{P : Stmt{ℓ}}{Q : Stmt{ℓ}} → ((¬ P) ∨ (¬ Q)) ← (¬ (P ∧ Q)))
    r wem {P = P} {Q = Q} npq with wem {P = P} | wem {P = Q}
    r wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introₗ nq  = [∨]-introₗ np
    r wem {P = P} {Q = Q} npq | [∨]-introₗ np  | [∨]-introᵣ nnq = [∨]-introₗ np
    r wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introₗ nq  = [∨]-introᵣ nq
    r wem {P = P} {Q = Q} npq | [∨]-introᵣ nnp | [∨]-introᵣ nnq = [∨]-introᵣ (q ↦ nnp (p ↦ npq ([∧]-intro p q)))

------------------------------------------
-- XOR

module _ {ℓ₁}{ℓ₂} {P : Stmt{ℓ₁}}{Q : Stmt{ℓ₂}} where
  [⊕][↔]-contradiction : (P ⊕ Q) → (P ↔ Q) → ⊥
  [⊕][↔]-contradiction ([⊕]-introₗ p nq) pq = nq([↔]-elimᵣ p pq)
  [⊕][↔]-contradiction ([⊕]-introᵣ q np) pq = np([↔]-elimₗ q pq)

  [⊕][∧]-contradiction : (P ⊕ Q) → (P ∧ Q) → ⊥
  [⊕][∧]-contradiction xor = [⊕][↔]-contradiction xor ∘ [∧]-to-[↔]

  [⊕]-not-both : (P ⊕ Q) → P → Q → ⊥
  [⊕]-not-both = Tuple.curry ∘ [⊕][∧]-contradiction

  [⊕]-not-left : (P ⊕ Q) → P → (¬ Q)
  [⊕]-not-left = [⊕]-not-both

  [⊕]-not-right : (P ⊕ Q) → Q → (¬ P)
  [⊕]-not-right = swap ∘ [⊕]-not-both

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

  [⊕]-or-not-both : (P ∨ Q) → ¬(P ∧ Q) → (P ⊕ Q)
  [⊕]-or-not-both or nand with or
  ... | [∨]-introₗ p = [⊕]-introₗ p (q ↦ nand([↔]-intro p q))
  ... | [∨]-introᵣ q = [⊕]-introᵣ q (p ↦ nand([↔]-intro p q))

  [⊕]-not-not-right : (P ⊕ Q) → (¬ P) → Q
  [⊕]-not-not-right ([⊕]-introₗ p nq) = [⊥]-elim ∘ apply p
  [⊕]-not-not-right ([⊕]-introᵣ q np) = const q

  [⊕]-not-not-left : (P ⊕ Q) → (¬ Q) → P
  [⊕]-not-not-left ([⊕]-introₗ p nq) = const p
  [⊕]-not-not-left ([⊕]-introᵣ q np) = [⊥]-elim ∘ apply q

  [⊕]-right-[↔] : (P ⊕ Q) → (¬ P) ↔ Q
  [⊕]-right-[↔] pq = [↔]-intro ([⊕]-not-right pq) ([⊕]-not-not-right pq)

  [⊕]-left-[↔] : (P ⊕ Q) → P ↔ (¬ Q)
  [⊕]-left-[↔] pq = [↔]-intro ([⊕]-not-not-left pq) ([⊕]-not-left pq)
