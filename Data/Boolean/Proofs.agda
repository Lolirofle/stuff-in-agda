module Data.Boolean.Proofs where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Logic.Propositional as Logic using (_∨_ ; _∧_ ; ¬_ ; _↔_ ; [⊤]-intro ; [↔]-intro ; [⊥]-elim)
open import Relator.Equals
open import Relator.Equals.Proofs
open import Type

-- TODO: Instances for these algebraic properties
-- TODO: More algebraic properties (associativity, commutativity and all the others)

[&&]-redundant : ∀{a} → (a && a ≡ a)
[&&]-redundant {𝑇} = [≡]-intro
[&&]-redundant {𝐹} = [≡]-intro
{-# REWRITE [&&]-redundant #-}

[||]-redundant : ∀{a} → (a || a ≡ a)
[||]-redundant {𝑇} = [≡]-intro
[||]-redundant {𝐹} = [≡]-intro
{-# REWRITE [||]-redundant #-}

[&&]-absorberₗ : ∀{a} → (𝐹 && a ≡ 𝐹)
[&&]-absorberₗ {𝑇} = [≡]-intro
[&&]-absorberₗ {𝐹} = [≡]-intro
{-# REWRITE [&&]-absorberₗ #-}

[&&]-absorberᵣ : ∀{a} → (a && 𝐹 ≡ 𝐹)
[&&]-absorberᵣ {𝑇} = [≡]-intro
[&&]-absorberᵣ {𝐹} = [≡]-intro
{-# REWRITE [&&]-absorberᵣ #-}

[||]-absorberₗ : ∀{a} → (𝑇 || a ≡ 𝑇)
[||]-absorberₗ {𝑇} = [≡]-intro
[||]-absorberₗ {𝐹} = [≡]-intro
{-# REWRITE [||]-absorberₗ #-}

[||]-absorberᵣ : ∀{a} → (a || 𝑇 ≡ 𝑇)
[||]-absorberᵣ {𝑇} = [≡]-intro
[||]-absorberᵣ {𝐹} = [≡]-intro
{-# REWRITE [||]-absorberᵣ #-}

[&&]-identityₗ : ∀{a} → (𝑇 && a ≡ a)
[&&]-identityₗ {𝑇} = [≡]-intro
[&&]-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [&&]-identityₗ #-}

[&&]-identityᵣ : ∀{a} → (a && 𝑇 ≡ a)
[&&]-identityᵣ {𝑇} = [≡]-intro
[&&]-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [&&]-identityᵣ #-}

[||]-identityₗ : ∀{a} → (𝐹 || a ≡ a)
[||]-identityₗ {𝑇} = [≡]-intro
[||]-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [||]-identityₗ #-}

[||]-identityᵣ : ∀{a} → (a || 𝐹 ≡ a)
[||]-identityᵣ {𝑇} = [≡]-intro
[||]-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [||]-identityᵣ #-}

[!!]-elim : ∀{a} → (! ! a ≡ a)
[!!]-elim {𝑇} = [≡]-intro
[!!]-elim {𝐹} = [≡]-intro
{-# REWRITE [!!]-elim #-}

[==]-identityₗ : ∀{a} → (𝑇 == a ≡ a)
[==]-identityₗ {𝑇} = [≡]-intro
[==]-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [==]-identityₗ #-}

[==]-identityᵣ : ∀{a} → (a == 𝑇 ≡ a)
[==]-identityᵣ {𝑇} = [≡]-intro
[==]-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [==]-identityᵣ #-}

[==]-anti-identityₗ : ∀{a} → (𝐹 == a ≡ ! a)
[==]-anti-identityₗ {𝑇} = [≡]-intro
[==]-anti-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [==]-anti-identityₗ #-}

[==]-anti-identityᵣ : ∀{a} → (a == 𝐹 ≡ ! a)
[==]-anti-identityᵣ {𝑇} = [≡]-intro
[==]-anti-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [==]-anti-identityᵣ #-}

[!=]-identityₗ : ∀{a} → (𝐹 != a ≡ a)
[!=]-identityₗ {𝑇} = [≡]-intro
[!=]-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [!=]-identityₗ #-}

[!=]-identityᵣ : ∀{a} → (a != 𝐹 ≡ a)
[!=]-identityᵣ {𝑇} = [≡]-intro
[!=]-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [!=]-identityᵣ #-}

[!=]-anti-identityₗ : ∀{a} → (𝑇 != a ≡ ! a)
[!=]-anti-identityₗ {𝑇} = [≡]-intro
[!=]-anti-identityₗ {𝐹} = [≡]-intro
{-# REWRITE [!=]-anti-identityₗ #-}

[!=]-anti-identityᵣ : ∀{a} → (a != 𝑇 ≡ ! a)
[!=]-anti-identityᵣ {𝑇} = [≡]-intro
[!=]-anti-identityᵣ {𝐹} = [≡]-intro
{-# REWRITE [!=]-anti-identityᵣ #-}

invert-[==][!=] : ∀{a b} → (!(a == b) ≡ (a != b))
invert-[==][!=] {𝑇}{𝑇} = [≡]-intro
invert-[==][!=] {𝑇}{𝐹} = [≡]-intro
invert-[==][!=] {𝐹}{𝑇} = [≡]-intro
invert-[==][!=] {𝐹}{𝐹} = [≡]-intro

invert-[!=][==] : ∀{a b} → (!(a != b) ≡ (a == b))
invert-[!=][==] {𝑇}{𝑇} = [≡]-intro
invert-[!=][==] {𝑇}{𝐹} = [≡]-intro
invert-[!=][==] {𝐹}{𝑇} = [≡]-intro
invert-[!=][==] {𝐹}{𝐹} = [≡]-intro

-- A boolean operation is either true or false
bivalence : ∀{a} → ((a ≡ 𝑇) ∨ (a ≡ 𝐹))
bivalence {𝑇} = Logic.[∨]-introₗ [≡]-intro
bivalence {𝐹} = Logic.[∨]-introᵣ [≡]-intro

-- A boolean operation is not both true and false at the same time
disjointness : ∀{a} → ¬((a ≡ 𝑇) ∧ (a ≡ 𝐹))
disjointness {𝑇} (Logic.[∧]-intro [≡]-intro ())
disjointness {𝐹} (Logic.[∧]-intro () [≡]-intro)

module 𝑇 where
  [∧]-intro : ∀{a b} → (a ≡ 𝑇) → (b ≡ 𝑇) → ((a && b) ≡ 𝑇)
  [∧]-intro [≡]-intro [≡]-intro = [≡]-intro

  [∨]-introₗ : ∀{a b} → (a ≡ 𝑇) → ((a || b) ≡ 𝑇)
  [∨]-introₗ {_}{𝑇} [≡]-intro = [≡]-intro
  [∨]-introₗ {_}{𝐹} [≡]-intro = [≡]-intro

  [∨]-introᵣ : ∀{a b} → (b ≡ 𝑇) → ((a || b) ≡ 𝑇)
  [∨]-introᵣ {𝑇}{_} [≡]-intro = [≡]-intro
  [∨]-introᵣ {𝐹}{_} [≡]-intro = [≡]-intro

  [∧]-elimₗ : ∀{a b} → ((a && b) ≡ 𝑇) → (a ≡ 𝑇)
  [∧]-elimₗ {𝑇}{𝑇} [≡]-intro = [≡]-intro
  [∧]-elimₗ {𝑇}{𝐹} ()
  [∧]-elimₗ {𝐹}{𝑇} ()
  [∧]-elimₗ {𝐹}{𝐹} ()

  [∧]-elimᵣ : ∀{a b} → ((a && b) ≡ 𝑇) → (b ≡ 𝑇)
  [∧]-elimᵣ {𝑇}{𝑇} [≡]-intro = [≡]-intro
  [∧]-elimᵣ {𝑇}{𝐹} ()
  [∧]-elimᵣ {𝐹}{𝑇} ()
  [∧]-elimᵣ {𝐹}{𝐹} ()

  [∨]-elim : ∀{a b}{ℓ₂}{φ : Set(ℓ₂)} → ((a ≡ 𝑇) → φ) → ((b ≡ 𝑇) → φ) → ((a || b) ≡ 𝑇) → φ
  [∨]-elim {𝑇}{𝑇}{_} f _ [≡]-intro = f [≡]-intro
  [∨]-elim {𝑇}{𝐹}{_} f _ [≡]-intro = f [≡]-intro
  [∨]-elim {𝐹}{𝑇}{_} _ f [≡]-intro = f [≡]-intro
  [∨]-elim {𝐹}{𝐹}{_} _ f ()

  [¬]-intro : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
  [¬]-intro [≡]-intro = [≡]-intro

  [¬]-elim : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
  [¬]-elim {𝑇} ()
  [¬]-elim {𝐹} [≡]-intro = [≡]-intro

  [∧]-transfer : ∀{a b} → ((a && b) ≡ 𝑇) ↔ (a ≡ 𝑇)∧(b ≡ 𝑇)
  [∧]-transfer = [↔]-intro
    (\(Logic.[∧]-intro l r) → [∧]-intro l r)
    (proof ↦ Logic.[∧]-intro ([∧]-elimₗ proof) ([∧]-elimᵣ proof))

  [∨]-transfer : ∀{a b} → ((a || b) ≡ 𝑇) ↔ (a ≡ 𝑇)∨(b ≡ 𝑇)
  [∨]-transfer = [↔]-intro
    (Logic.[∨]-elim [∨]-introₗ [∨]-introᵣ)
    ([∨]-elim Logic.[∨]-introₗ Logic.[∨]-introᵣ)

  [¬]-transfer : ∀{a} → (! a ≡ 𝑇) ↔ ¬(a ≡ 𝑇)
  [¬]-transfer {a} = [↔]-intro (l{a}) (r{a}) where
    l : ∀{a} → (! a ≡ 𝑇) ← ¬(a ≡ 𝑇)
    l {𝐹} _ = [≡]-intro
    l {𝑇} f = [⊥]-elim (f [≡]-intro)

    r : ∀{a} → (! a ≡ 𝑇) → ¬(a ≡ 𝑇)
    r {𝑇} () _
    r {𝐹} _ ()

  [≡]-transfer : ∀{a b} → ((a == b) ≡ 𝑇) ↔ (a ≡ b)
  [≡]-transfer {𝑇}{𝑇} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ [≡]-intro)
  [≡]-transfer {𝐹}{𝑇} = [↔]-intro (\()) (\())
  [≡]-transfer {𝑇}{𝐹} = [↔]-intro (\()) (\())
  [≡]-transfer {𝐹}{𝐹} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ [≡]-intro)

  [≢]-transfer : ∀{a b} → ((a != b) ≡ 𝑇) ↔ (a ≢ b)
  [≢]-transfer {𝑇}{𝑇} = [↔]-intro (ab ↦ [⊥]-elim(ab [≡]-intro)) (\())
  [≢]-transfer {𝐹}{𝑇} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ \())
  [≢]-transfer {𝑇}{𝐹} = [↔]-intro (_ ↦ [≡]-intro) (_ ↦ \())
  [≢]-transfer {𝐹}{𝐹} = [↔]-intro (ab ↦ [⊥]-elim(ab [≡]-intro)) (\())

module 𝐹 where
  [∧]-introₗ : ∀{a b} → (a ≡ 𝐹) → ((a && b) ≡ 𝐹)
  [∧]-introₗ {_}{𝑇} [≡]-intro = [≡]-intro
  [∧]-introₗ {_}{𝐹} [≡]-intro = [≡]-intro

  [∧]-introᵣ : ∀{a b} → (b ≡ 𝐹) → ((a && b) ≡ 𝐹)
  [∧]-introᵣ {𝑇}{_} [≡]-intro = [≡]-intro
  [∧]-introᵣ {𝐹}{_} [≡]-intro = [≡]-intro

  [∨]-intro : ∀{a b} → (a ≡ 𝐹) → (b ≡ 𝐹) → ((a || b) ≡ 𝐹)
  [∨]-intro [≡]-intro [≡]-intro = [≡]-intro

  [¬]-intro : ∀{a} → (! a ≡ 𝑇) → (a ≡ 𝐹)
  [¬]-intro = 𝑇.[¬]-elim

  [¬]-elim : ∀{a} → (a ≡ 𝐹) → (! a ≡ 𝑇)
  [¬]-elim = 𝑇.[¬]-intro

[≢][𝑇]-is-[𝐹] : ∀{a} → (a ≢ 𝑇) ↔ (a ≡ 𝐹)
[≢][𝑇]-is-[𝐹] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝑇) → (a ≡ 𝐹)
  r {𝑇} (a≢𝑇) = [⊥]-elim ((a≢𝑇) ([≡]-intro))
  r {𝐹} (a≢𝑇) = [≡]-intro

  l : ∀{a} → (a ≢ 𝑇) ← (a ≡ 𝐹)
  l {𝑇} ()
  l {𝐹} (a≡𝐹) ()

[≢][𝐹]-is-[𝑇] : ∀{a} → (a ≢ 𝐹) ↔ (a ≡ 𝑇)
[≢][𝐹]-is-[𝑇] {a} = [↔]-intro (l{a}) (r{a}) where
  r : ∀{a} → (a ≢ 𝐹) → (a ≡ 𝑇)
  r {𝑇} (a≢𝐹) = [≡]-intro
  r {𝐹} (a≢𝐹) = [⊥]-elim ((a≢𝐹) ([≡]-intro))

  l : ∀{a} → (a ≢ 𝐹) ← (a ≡ 𝑇)
  l {𝑇} (a≡𝑇) ()
  l {𝐹} ()


module _ {ℓ} {T : Type{ℓ}} {x y : T} where
  if-and : ∀{B₁ B₂} → (if (B₁ && B₂) then x else y ≡ if B₁ then (if B₂ then x else y) else y)
  if-and {𝐹}{𝐹} = [≡]-intro
  if-and {𝐹}{𝑇} = [≡]-intro
  if-and {𝑇}{𝐹} = [≡]-intro
  if-and {𝑇}{𝑇} = [≡]-intro

  if-or : ∀{B₁ B₂} → (if (B₁ || B₂) then x else y ≡ if B₁ then x else if B₂ then x else y)
  if-or {𝐹}{𝐹} = [≡]-intro
  if-or {𝐹}{𝑇} = [≡]-intro
  if-or {𝑇}{𝐹} = [≡]-intro
  if-or {𝑇}{𝑇} = [≡]-intro

  if-not : ∀{B} → (if (! B) then x else y ≡ if B then y else x)
  if-not {𝐹} = [≡]-intro
  if-not {𝑇} = [≡]-intro

module _ {ℓ} {T : Type{ℓ}} {x : T} where
  if-then-redundant : ∀{B} → (if B then x else x ≡ x)
  if-then-redundant {𝐹} = [≡]-intro
  if-then-redundant {𝑇} = [≡]-intro

{-# REWRITE if-then-redundant #-}

module _ {ℓ} {T : Type{ℓ}} where
  if-then-bool-redundant1 : ∀{B} → (if B then 𝑇 else 𝐹 ≡ B)
  if-then-bool-redundant1 {𝐹} = [≡]-intro
  if-then-bool-redundant1 {𝑇} = [≡]-intro

  if-then-bool-redundant2 : ∀{B} → (if B then 𝐹 else 𝑇 ≡ ! B)
  if-then-bool-redundant2 {𝐹} = [≡]-intro
  if-then-bool-redundant2 {𝑇} = [≡]-intro

{-# REWRITE if-then-bool-redundant1 #-}
{-# REWRITE if-then-bool-redundant2 #-}

module _ {ℓ₁ ℓ₂ ℓ₃} {T : Type{ℓ₁}} {x y : T} {P : T → Type{ℓ₂}} {Q : Type{ℓ₃}} where
  if-elim : ∀{B} → P(if B then x else y) → (P(x) → Q) → (P(y) → Q) → Q
  if-elim{𝑇} p pxq pyq = pxq p
  if-elim{𝐹} p pxq pyq = pyq p
