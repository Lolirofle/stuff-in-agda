module Data.Boolean.Stmt.Proofs where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs hiding (bivalence ; disjointness)
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional as Logic using (_∨_ ; _∧_ ; ¬_ ; _↔_ ; [⊤]-intro ; [↔]-intro ; [⊥]-elim)
open import Relator.Equals
open import Type

-- A boolean operation is either true or false
bivalence : ∀{a} → (IsTrue(a) ∨ IsFalse(a))
bivalence {𝑇} = Logic.[∨]-introₗ [⊤]-intro
bivalence {𝐹} = Logic.[∨]-introᵣ [⊤]-intro

-- A boolean operation is not both true and false at the same time
disjointness : ∀{a} → ¬(IsTrue(a) ∧ IsFalse(a))
disjointness {𝑇} (Logic.[∧]-intro [⊤]-intro ())
disjointness {𝐹} (Logic.[∧]-intro () [⊤]-intro)

module IsTrue where
  [∧]-intro : ∀{a b} → IsTrue(a) → IsTrue(b) → IsTrue(a && b)
  [∧]-intro {𝑇} {b} ta tb = tb
  [∧]-intro {𝐹} {b} ta tb = ta

  [∨]-introₗ : ∀{a b} → IsTrue(a) → IsTrue(a || b)
  [∨]-introₗ {_}{𝑇} _ = [⊤]-intro
  [∨]-introₗ {_}{𝐹} = id

  [∨]-introᵣ : ∀{a b} → IsTrue(b) → IsTrue(a || b)
  [∨]-introᵣ {𝑇}{_} _ = [⊤]-intro
  [∨]-introᵣ {𝐹}{_} = id

  [∧]-elimₗ : ∀{a b} → IsTrue(a && b) → IsTrue(a)
  [∧]-elimₗ {𝑇}{𝑇} [⊤]-intro = [⊤]-intro
  [∧]-elimₗ {𝑇}{𝐹} ()
  [∧]-elimₗ {𝐹}{𝑇} ()
  [∧]-elimₗ {𝐹}{𝐹} ()

  [∧]-elimᵣ : ∀{a b} → IsTrue(a && b) → IsTrue(b)
  [∧]-elimᵣ {𝑇}{𝑇} [⊤]-intro = [⊤]-intro
  [∧]-elimᵣ {𝑇}{𝐹} ()
  [∧]-elimᵣ {𝐹}{𝑇} ()
  [∧]-elimᵣ {𝐹}{𝐹} ()

  [∨]-elim : ∀{ℓ₂}{φ : Type{ℓ₂}}{a b} → (IsTrue(a) → φ) → (IsTrue(b) → φ) → IsTrue(a || b) → φ
  [∨]-elim {_}{_}{𝑇}{𝑇} f _ [⊤]-intro = f [⊤]-intro
  [∨]-elim {_}{_}{𝑇}{𝐹} f _ [⊤]-intro = f [⊤]-intro
  [∨]-elim {_}{_}{𝐹}{𝑇} _ f [⊤]-intro = f [⊤]-intro
  [∨]-elim {_}{_}{𝐹}{𝐹} _ f ()

  [¬]-intro : ∀{a} → IsFalse(a) → IsTrue(! a)
  [¬]-intro {𝐹} fa = [⊤]-intro

  [¬]-elim : ∀{a} → IsTrue(! a) → IsFalse(a)
  [¬]-elim {𝑇} ()
  [¬]-elim {𝐹} [⊤]-intro = [⊤]-intro

  is-𝑇 : ∀{a} → IsTrue(a) ↔ (a ≡ 𝑇)
  is-𝑇 {a} = [↔]-intro (l{a}) (r{a}) where
    r : ∀ {a} → IsTrue(a) → (a ≡ 𝑇)
    r {𝑇} _ = [≡]-intro
    r {𝐹} ()

    l : ∀ {a} → IsTrue(a) ← (a ≡ 𝑇)
    l [≡]-intro = [⊤]-intro

  preserves-[&&][∧] : ∀{a b} → IsTrue(a && b) ↔ IsTrue(a) ∧ IsTrue(b)
  preserves-[&&][∧] = [↔]-intro
    (\{(Logic.[∧]-intro l r) → [∧]-intro l r})
    (proof ↦ Logic.[∧]-intro ([∧]-elimₗ proof) ([∧]-elimᵣ proof))

  preserves-[||][∨] : ∀{a b} → IsTrue(a || b) ↔ IsTrue(a) ∨ IsTrue(b)
  preserves-[||][∨] = [↔]-intro
    (Logic.[∨]-elim [∨]-introₗ [∨]-introᵣ)
    ([∨]-elim Logic.[∨]-introₗ Logic.[∨]-introᵣ)

  preserves-[!][¬] : ∀{a} → IsTrue(! a) ↔ (¬ IsTrue(a))
  preserves-[!][¬] {a} = [↔]-intro (l{a}) (r{a}) where
    l : ∀{a} → IsTrue(! a) ← (¬ IsTrue(a))
    l {𝐹} _ = [⊤]-intro
    l {𝑇} f = [⊥]-elim (f [⊤]-intro)

    r : ∀{a} → IsTrue(! a) → (¬ IsTrue(a))
    r {𝑇} () _
    r {𝐹} _ ()

module IsFalse where
  [∧]-introₗ : ∀{a b} → IsFalse(a) → IsFalse(a && b)
  [∧]-introₗ {_}{𝑇} = id
  [∧]-introₗ {_}{𝐹} _ = [⊤]-intro

  [∧]-introᵣ : ∀{a b} → IsFalse(b) → IsFalse(a && b)
  [∧]-introᵣ {𝑇}{_} = id
  [∧]-introᵣ {𝐹}{_} _ = [⊤]-intro

  [∨]-intro : ∀{a b} → IsFalse(a) → IsFalse(b) → IsFalse(a || b)
  [∨]-intro {𝑇} fa fb = fa
  [∨]-intro {𝐹} fa fb = fb

  [¬]-intro : ∀{a} → IsTrue(a) → IsFalse(! a)
  [¬]-intro = id

  [¬]-elim : ∀{a} → IsFalse(! a) → IsTrue(a)
  [¬]-elim = id

  is-𝐹 : ∀{a} → IsFalse(a) ↔ (a ≡ 𝐹)
  is-𝐹 {a} = [↔]-intro (l{a}) (r{a}) where
    r : ∀{a} → IsFalse(a) → (a ≡ 𝐹)
    r {𝑇} ()
    r {𝐹} _ = [≡]-intro

    l : ∀{a} → IsFalse(a) ← (a ≡ 𝐹)
    l [≡]-intro = [⊤]-intro

true-false-opposites : ∀{a} → IsTrue(a) ↔ (¬ IsFalse(a))
true-false-opposites {𝑇} = [↔]-intro (const [⊤]-intro) (const id)
true-false-opposites {𝐹} = [↔]-intro (_$    [⊤]-intro) const

false-true-opposites : ∀{a} → IsFalse(a) ↔ (¬ IsTrue(a))
false-true-opposites {𝑇} = [↔]-intro (_$    [⊤]-intro) const
false-true-opposites {𝐹} = [↔]-intro (const [⊤]-intro) (const id)
